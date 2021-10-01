//! Functions for normalising various parts of the build.
//! The general goal is for the same input to generate the
//! same ostree commit hash each time.

// Copyright (C) 2021 Oracle and/or its affiliates.
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::nameservice::shadow::parse_shadow_content;
use anyhow::{anyhow, Result};
use fn_error_context::context;
use lazy_static::lazy_static;
use std::convert::TryInto;
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};
use std::path::Path;

lazy_static! {
    static ref SOURCE_DATE_EPOCH_RAW: Option<String> = std::env::var("SOURCE_DATE_EPOCH").ok();
    static ref SOURCE_DATE_EPOCH: Option<i64> = SOURCE_DATE_EPOCH_RAW
        .as_ref()
        .map(|s| s.parse::<i64>().expect("bad number in SOURCE_DATE_EPOCH"));
}

pub(crate) fn source_date_epoch_raw() -> Option<&'static str> {
    SOURCE_DATE_EPOCH_RAW.as_ref().map(|s| s.as_str())
}

#[context("Rewriting /etc/shadow to remove lstchg field")]
pub(crate) fn normalize_etc_shadow(rootfs: &openat::Dir) -> Result<()> {
    // Read in existing entries.
    let mut shadow = rootfs.update_file("usr/etc/shadow", 0o400)?;
    let entries = parse_shadow_content(BufReader::new(&mut shadow))?;

    // Go back to the start and truncate the file.
    shadow.seek(SeekFrom::Start(0))?;
    shadow.set_len(0)?;

    for mut entry in entries {
        // Entries starting with `!` or `*` indicate accounts that are
        // either locked or not using passwords. The last password
        // change value can be safely blanked for these.
        if entry.pwdp.starts_with('!') || entry.pwdp.starts_with('*') {
            entry.lstchg = None;
        }

        entry.to_writer(&mut shadow)?;
    }

    Ok(())
}

const RPM_HEADER_MAGIC: [u8; 8] = [0x8E, 0xAD, 0xE8, 0x01, 0x00, 0x00, 0x00, 0x00];
const RPMTAG_INSTALLTIME: u32 = 1008;
const RPMTAG_INSTALLTID: u32 = 1128;

#[context("Normalizing rpmdb timestamps for build stability")]
pub(crate) fn rewrite_rpmdb_timestamps<F: Read + Write + Seek>(rpmdb: &mut F) -> Result<()> {
    let source_date_epoch = if let Some(source_date_epoch) = *SOURCE_DATE_EPOCH {
        source_date_epoch as u32
    } else {
        return Ok(());
    };

    // Remember where we started
    let pos = rpmdb.stream_position()?;

    let mut buffer: [u8; 16] = [0; 16];
    let install_tid = source_date_epoch;
    let mut install_time = source_date_epoch;

    loop {
        // Read in a header record
        match rpmdb.read_exact(&mut buffer) {
            Err(ref e) if e.kind() == std::io::ErrorKind::UnexpectedEof => break,
            Err(e) => Err(e)?,
            _ => (),
        };

        // Make sure things are sane
        if buffer[..8] != RPM_HEADER_MAGIC {
            return Err(anyhow!("Bad RPM header magic in RPM database"));
        }

        // Grab the count of index records and the size of the data blob
        let record_count = u32::from_be_bytes(buffer[8..12].try_into()?);
        let data_size = u32::from_be_bytes(buffer[12..].try_into()?);

        // Loop through the records looking for ones that point at things
        // that are, or are derived from, timestamps
        let mut offsets = Vec::new();
        for _ in 0..record_count {
            rpmdb.read_exact(&mut buffer)?;

            let tag = u32::from_be_bytes(buffer[..4].try_into()?);
            if tag == RPMTAG_INSTALLTIME || tag == RPMTAG_INSTALLTID {
                offsets.push((tag, u32::from_be_bytes(buffer[8..12].try_into()?)));
            }
        }

        // Work through the data blob replacing the timestamp-derived values
        // with the timestamp we want
        offsets.sort_unstable_by_key(|(_, offset)| *offset);
        let mut offset = 0;
        for (tag, value_offset) in offsets {
            rpmdb.seek(std::io::SeekFrom::Current((value_offset - offset) as i64))?;
            if tag == RPMTAG_INSTALLTID {
                rpmdb.write_all(&install_tid.to_be_bytes())?;
            } else if tag == RPMTAG_INSTALLTIME {
                rpmdb.write_all(&install_time.to_be_bytes())?;
                install_time += 1;
            }
            offset = value_offset + std::mem::size_of::<u32>() as u32;
        }

        // Move to the next record
        rpmdb.seek(std::io::SeekFrom::Current((data_size - offset) as i64))?;
    }

    // Seek back to where we were before
    rpmdb.seek(std::io::SeekFrom::Start(pos))?;

    Ok(())
}

#[context("Rewriting rpmdb database files for build stability")]
pub(crate) fn normalize_rpmdb(rootfs: &openat::Dir, rpmdb_path: impl AsRef<Path>) -> Result<()> {
    let source_date_epoch = if let Some(source_date_epoch) = *SOURCE_DATE_EPOCH {
        source_date_epoch as u32
    } else {
        return Ok(());
    };

    let mut db_backend = None;

    let macros = BufReader::new(rootfs.open_file("usr/lib/rpm/macros")?);
    for line in macros.lines() {
        let line = line?;
        if line.is_empty() {
            continue;
        }

        let mut bits = line.split(char::is_whitespace).filter(|s| !s.is_empty());
        if let Some(m) = bits.next() {
            if m == "%_db_backend" {
                db_backend = bits.last().map(|s| s.to_string());
                break;
            }
        };
    }

    let db_backend = db_backend.ok_or_else(|| anyhow!("Unable to determine rpmdb backend"))?;

    match db_backend.as_str() {
        "bdb" | "b-d-b" => rpmdb_bdb::normalize_rpmdb_bdb(rootfs, rpmdb_path, source_date_epoch),
        "ndb" => Ok(()),
        "sqlite" => Ok(()),
        _ => Err(anyhow!("Unknown rpmdb backend: {}", db_backend)),
    }
}

mod rpmdb_bdb {
    use anyhow::{anyhow, Context, Result};
    use binread::{BinRead, BinReaderExt};
    use lazy_static::lazy_static;
    use openat::SimpleType;
    use sha2::Digest;
    use std::ffi::OsStr;
    use std::io::{Read, Seek, SeekFrom, Write};
    use std::os::unix::io::AsRawFd;
    use std::path::{Path, PathBuf};
    use subprocess::{Exec, Redirection};

    #[derive(BinRead, Debug, Clone, Copy, PartialEq, Eq)]
    #[repr(u8)]
    #[br(repr=u8)]
    enum PageType {
        IBTree = 3,
        LBTree = 5,
        Overflow = 7,
        HashMeta = 8,
        BTreeMeta = 9,
        Hash = 13,
    }

    #[derive(BinRead, Debug)]
    #[br(little)]
    struct MetaHeader {
        lsn: u64,
        pgno: u32,
        magic: u32,
        version: u32,
        pagesize: u32,
        encrypt_alg: u8,
        page_type: PageType,
        metaflags: u8,
        unused1: u8,
        free: u32,
        last_pgno: u32,
        nparts: u32,
        key_count: u32,
        record_count: u32,
        flags: u32,
        uid: [u8; 20],
    }

    const BTREE_MAGIC: u32 = 0x00053162;
    const HASH_MAGIC: u32 = 0x00061561;
    const PAGE_HEADER_SIZE: u16 = 26;
    const PAGE_HEADER_MAGIC_OFFSET: u64 = 0x34;

    #[derive(BinRead, Debug)]
    #[br(little)]
    struct PageHeader {
        lsn: u64,
        pgno: u32,
        prev_pgno: u32,
        next_pgno: u32,
        entries: u16,
        hf_offset: u16,
        level: u8,
        page_type: PageType,
    }

    #[derive(BinRead, Debug)]
    #[br(repr=u8)]
    #[repr(u8)]
    enum BTreeItemType {
        KeyData = 1,
        Duplicate = 2,
        Overflow = 3,
    }

    #[derive(BinRead, Debug)]
    #[br(little)]
    struct BTreeItem {
        len: u16,
        item_type: BTreeItemType,
    }

    #[derive(BinRead, Debug)]
    #[br(repr=u8)]
    #[repr(u8)]
    enum HashItemType {
        KeyData = 1,
        Duplicate = 2,
        Offpage = 3,
        OffDup = 4,
    }

    lazy_static! {
        static ref PROC_SELF_CWD: PathBuf = PathBuf::from("/proc/self/cwd");
        static ref PROC_SELF_FD: PathBuf = PathBuf::from("/proc/self/fd");
    }

    pub(super) fn normalize_rpmdb_bdb<P: AsRef<Path>>(
        rootfs: &openat::Dir,
        rpmdb_path: P,
        timestamp: u32,
    ) -> Result<()> {
        let rpmdb_path = rpmdb_path.as_ref();

        for entry in rootfs.list_dir(rpmdb_path)? {
            let entry = entry?;

            match entry.simple_type() {
                Some(SimpleType::File) => (),
                _ => continue,
            };

            if let Some(filename) = entry.file_name().to_str() {
                if filename.starts_with('.') || filename.starts_with("__db") {
                    continue;
                }
            } else {
                continue;
            }

            let path = rpmdb_path.join(entry.file_name());

            let old_digest = sha2::Sha256::digest(
                Exec::cmd("db_dump")
                    .args(&[PROC_SELF_CWD.join(&path)])
                    .cwd(PROC_SELF_FD.join(rootfs.as_raw_fd().to_string()))
                    .stdout(Redirection::Pipe)
                    .capture()
                    .context("pre-normalization data dump")?
                    .stdout
                    .as_slice(),
            );

            {
                let mut file_id = sha2::Sha256::new();
                file_id.update(timestamp.to_be_bytes());
                file_id.update(format!("rpm/{}", entry.file_name().to_str().unwrap()).as_bytes());
                let file_id = &file_id.finalize()[..20];

                let mut db = rootfs.update_file(&path, 0o644)?;
                let meta_header: MetaHeader = db.read_le()?;

                match (meta_header.magic, meta_header.page_type) {
                    (BTREE_MAGIC, PageType::BTreeMeta) => (),
                    (HASH_MAGIC, PageType::HashMeta) => (),
                    _ => continue,
                };

                db.seek(SeekFrom::Start(PAGE_HEADER_MAGIC_OFFSET))?;
                db.write_all(file_id)?;

                for pageno in 1..meta_header.last_pgno + 1 {
                    db.seek(SeekFrom::Start((pageno * meta_header.pagesize) as u64))?;

                    let header: PageHeader = db.read_le()?;

                    if header.page_type == PageType::Overflow {
                        db.seek(SeekFrom::Current(header.hf_offset as i64))?;
                        let fill_length =
                            meta_header.pagesize - (PAGE_HEADER_SIZE + header.hf_offset) as u32;
                        std::io::copy(
                            &mut std::io::repeat(b'\x00').take(fill_length as u64),
                            &mut db,
                        )?;
                        continue;
                    }

                    let mut offsets: Vec<u16> = Vec::new();

                    for _ in 0..header.entries {
                        offsets.push(db.read_le()?);
                    }

                    offsets.sort_unstable();

                    let empty = if offsets.is_empty() {
                        meta_header.pagesize - PAGE_HEADER_SIZE as u32
                    } else {
                        *offsets.first().unwrap() as u32
                            - (PAGE_HEADER_SIZE + header.entries * 2) as u32
                    };

                    std::io::copy(&mut std::io::repeat(b'\x00').take(empty as u64), &mut db)?;

                    let mut offset_iter = offsets.into_iter().peekable();
                    while let Some(offset) = offset_iter.next() {
                        db.seek(SeekFrom::Start(
                            (pageno * meta_header.pagesize + offset as u32) as u64,
                        ))?;

                        if matches!(header.page_type, PageType::IBTree | PageType::LBTree) {
                            let item: BTreeItem = db.read_le()?;
                            if header.page_type == PageType::IBTree {
                                db.write_all(b"\x00")?;
                            } else if header.page_type == PageType::LBTree {
                                if let BTreeItemType::Overflow = item.item_type {
                                    db.seek(SeekFrom::Current(-3))?;
                                    db.write_all(b"\x00\x00")?;
                                } else if let BTreeItemType::KeyData = item.item_type {
                                    let next_offset = if let Some(next) = offset_iter.peek() {
                                        *next
                                    } else {
                                        meta_header.pagesize as u16
                                    };
                                    let remainder = next_offset - (offset + 3 + item.len);
                                    if remainder != 0 {
                                        db.seek(SeekFrom::Current(item.len as i64))?;
                                        std::io::copy(
                                            &mut std::io::repeat(b'\x00').take(remainder as u64),
                                            &mut db,
                                        )?;
                                    }
                                }
                            }
                        } else if header.page_type == PageType::Hash {
                            let item_type: HashItemType = db.read_le()?;

                            if let HashItemType::Offpage = item_type {
                                db.write_all(b"\x00\x00\x00")?;
                            }
                        }
                    }
                }

                db.flush()?;
            }

            let r = Exec::cmd("db_verify")
                .args(&[OsStr::new("-q"), PROC_SELF_CWD.join(&path).as_os_str()])
                .cwd(PROC_SELF_FD.join(rootfs.as_raw_fd().to_string()))
                .join()?;
            if !r.success() {
                return Err(anyhow!("post-normalization verification failed"));
            }

            let new_digest = sha2::Sha256::digest(
                Exec::cmd("db_dump")
                    .args(&[PROC_SELF_CWD.join(&path)])
                    .cwd(PROC_SELF_FD.join(rootfs.as_raw_fd().to_string()))
                    .stdout(Redirection::Pipe)
                    .capture()
                    .context("post-normalization data dump")?
                    .stdout
                    .as_slice(),
            );

            if new_digest != old_digest {
                return Err(anyhow!("file data changed during normalization"));
            }
        }

        Ok(())
    }
}
