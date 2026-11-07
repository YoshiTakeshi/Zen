//! The block log on disk (Justus L. Ludovic).
//!
//! `<dir>/blocks.log` is `ZENLOG01` followed by records `len u32 | crc32 u32 | payload`, appended one write and one `sync_data` per block.
//! Opening scans every record once: a torn tail (a crash in the middle of an append) is cut off and counted in `repaired`; a damaged record
//! with more data after it is an error, never silently skipped. Blocks are read back by offset, so a node keeps only the recent blocks in memory.
//! `<dir>/LOCK` keeps a second node from opening the same directory.
use anyhow::{anyhow, bail, Result};
use std::fs::{File, OpenOptions};
use std::os::unix::fs::FileExt;
use std::path::Path;
use std::sync::Mutex;

const MAGIC: &[u8; 8] = b"ZENLOG01";
const MAX_RECORD: u32 = 64 << 20;

pub fn crc32(data: &[u8]) -> u32 {
    let mut table = [0u32; 256];
    for i in 0..256u32 { let mut c = i; for _ in 0..8 { c = if c & 1 == 1 { 0xEDB8_8320 ^ (c >> 1) } else { c >> 1 }; } table[i as usize] = c; }
    let mut crc = !0u32;
    for b in data { crc = table[((crc ^ *b as u32) & 0xff) as usize] ^ (crc >> 8); }
    !crc
}


/// little-endian writer / bounds-checked reader for the snapshot files
pub struct Wr(pub Vec<u8>);
impl Wr {
    pub fn new() -> Wr { Wr(vec![]) }
    pub fn u8(&mut self, x: u8) { self.0.push(x); }
    pub fn u32(&mut self, x: u32) { self.0.extend_from_slice(&x.to_le_bytes()); }
    pub fn u64(&mut self, x: u64) { self.0.extend_from_slice(&x.to_le_bytes()); }
    pub fn u128(&mut self, x: u128) { self.0.extend_from_slice(&x.to_le_bytes()); }
    pub fn raw(&mut self, x: &[u8]) { self.0.extend_from_slice(x); }
}
pub struct Rd<'a> { b: &'a [u8], p: usize }
impl<'a> Rd<'a> {
    pub fn new(b: &'a [u8]) -> Rd<'a> { Rd { b, p: 0 } }
    pub fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.p.checked_add(n).filter(|e| *e <= self.b.len()).ok_or_else(|| anyhow!("snapshot ends early"))?;
        let r = &self.b[self.p..end]; self.p = end; Ok(r)
    }
    pub fn u8(&mut self) -> Result<u8> { Ok(self.take(1)?[0]) }
    pub fn u32(&mut self) -> Result<u32> { Ok(u32::from_le_bytes(self.take(4)?.try_into()?)) }
    pub fn u64(&mut self) -> Result<u64> { Ok(u64::from_le_bytes(self.take(8)?.try_into()?)) }
    pub fn u128(&mut self) -> Result<u128> { Ok(u128::from_le_bytes(self.take(16)?.try_into()?)) }
    /// a count of items of at least `min` bytes each: refuses a count the rest of the file cannot hold
    pub fn count(&mut self, min: usize) -> Result<usize> {
        let n = self.u64()?;
        if n > ((self.b.len() - self.p) / min.max(1)) as u64 { bail!("snapshot count {n} is more than the file can hold"); }
        Ok(n as usize)
    }
    pub fn done(&self) -> Result<()> { if self.p != self.b.len() { bail!("trailing bytes in the snapshot"); } Ok(()) }
}

struct Inner { file: File, end: u64, records: Vec<(u64, u32)> }
pub struct Store {
    inner: Mutex<Inner>,
    _lock: Option<File>,
    /// bytes cut from the end when the log was opened (0 when it was whole)
    pub repaired: u64,
}

impl Store {
    /// open (or create) the log in `dir`; with `lock`, fail when another node holds the directory
    pub fn open(dir: &Path, lock: bool) -> Result<Store> {
        std::fs::create_dir_all(dir)?;
        let lockf = if lock {
            let f = OpenOptions::new().create(true).write(true).open(dir.join("LOCK"))?;
            f.try_lock().map_err(|_| anyhow!("{} is in use by another node", dir.display()))?;
            Some(f)
        } else { None };
        let path = dir.join("blocks.log");
        let file = OpenOptions::new().read(true).write(true).create(true).open(&path)?;
        let len = file.metadata()?.len();
        let mut repaired = 0;
        let mut end = len;
        let mut records = vec![];
        if len < 8 {
            let mut have = vec![0u8; len as usize];
            file.read_exact_at(&mut have, 0)?;
            if have != MAGIC[..len as usize] { bail!("{} is not a Zen block log", path.display()); }
            file.set_len(0)?; file.write_all_at(MAGIC, 0)?; file.sync_data()?;
            repaired = len; end = 8;
        } else {
            let mut m = [0u8; 8];
            file.read_exact_at(&mut m, 0)?;
            if &m != MAGIC { bail!("{} is not a Zen block log (or is in an older format)", path.display()); }
            let mut pos = 8u64;
            loop {
                if pos == len { break; }
                if len - pos < 8 { break; }                                   // a torn record header
                let mut h = [0u8; 8];
                file.read_exact_at(&mut h, pos)?;
                let n = u32::from_le_bytes(h[..4].try_into().unwrap());
                let crc = u32::from_le_bytes(h[4..].try_into().unwrap());
                if n > MAX_RECORD { bail!("damaged record at byte {pos} of {} (length {n})", path.display()); }
                let stop = pos + 8 + n as u64;
                if stop > len { break; }                                      // a torn record body
                let mut body = vec![0u8; n as usize];
                file.read_exact_at(&mut body, pos + 8)?;
                if crc32(&body) != crc {
                    if stop == len { break; }                                 // the last record only half written
                    bail!("damaged record at byte {pos} of {}: checksum differs, and more data follows", path.display());
                }
                records.push((pos + 8, n));
                pos = stop;
            }
            if pos < len { file.set_len(pos)?; file.sync_data()?; repaired = len - pos; }
            end = pos;
        }
        Ok(Store { inner: Mutex::new(Inner { file, end, records }), _lock: lockf, repaired })
    }
    /// append one record and make it durable; returns where its payload is
    pub fn append(&self, payload: &[u8]) -> Result<(u64, u32)> {
        if payload.len() as u64 > MAX_RECORD as u64 { bail!("record too large"); }
        let mut g = self.inner.lock().unwrap();
        let mut buf = Vec::with_capacity(8 + payload.len());
        buf.extend_from_slice(&(payload.len() as u32).to_le_bytes());
        buf.extend_from_slice(&crc32(payload).to_le_bytes());
        buf.extend_from_slice(payload);
        let at = g.end;
        g.file.write_all_at(&buf, at)?;
        g.file.sync_data()?;
        g.end = at + buf.len() as u64;
        let loc = (at + 8, payload.len() as u32);
        g.records.push(loc);
        Ok(loc)
    }
    pub fn read(&self, loc: (u64, u32)) -> Result<Vec<u8>> {
        let g = self.inner.lock().unwrap();
        let mut b = vec![0u8; loc.1 as usize];
        g.file.read_exact_at(&mut b, loc.0)?;
        Ok(b)
    }
    pub fn len(&self) -> usize { self.inner.lock().unwrap().records.len() }
    pub fn record(&self, i: usize) -> Option<(u64, u32)> { self.inner.lock().unwrap().records.get(i).copied() }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn dir(name: &str) -> std::path::PathBuf {
        let d = std::env::temp_dir().join(format!("zen-store-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d); d
    }
    #[test]
    fn crc32_matches_the_standard_check_value() { assert_eq!(crc32(b"123456789"), 0xCBF4_3926); }
    #[test]
    fn records_come_back_and_survive_a_reopen() {
        let d = dir("basic");
        let s = Store::open(&d, false).unwrap();
        let locs: Vec<_> = (0..20u8).map(|i| s.append(&vec![i; 1 + i as usize * 7]).unwrap()).collect();
        drop(s);
        let s = Store::open(&d, false).unwrap();
        assert_eq!((s.len(), s.repaired), (20, 0));
        for (i, loc) in locs.iter().enumerate() { assert_eq!(s.read(s.record(i).unwrap()).unwrap(), vec![i as u8; 1 + i * 7]); assert_eq!(s.record(i), Some(*loc)); }
        let _ = std::fs::remove_dir_all(&d);
    }
    #[test]
    fn a_torn_tail_is_cut_at_every_possible_length() {
        let d = dir("torn");
        let s = Store::open(&d, false).unwrap();
        for i in 0..3u8 { s.append(&vec![i; 50]).unwrap(); }
        drop(s);
        let path = d.join("blocks.log");
        let whole = std::fs::read(&path).unwrap();
        let rec = 8 + 50;
        // cut anywhere inside the last record, and anywhere inside the header: the first two records (or none) survive
        for cut in (8 + 2 * rec)..whole.len() {
            std::fs::write(&path, &whole[..cut]).unwrap();
            let s = Store::open(&d, false).unwrap();
            assert_eq!(s.len(), 2, "cut at {cut}");
            assert_eq!(s.repaired, (cut - (8 + 2 * rec)) as u64);
            s.append(&[9; 5]).unwrap();
            drop(s);
            assert_eq!(Store::open(&d, false).unwrap().len(), 3, "an append after the repair lands cleanly");
        }
        for cut in 0..8 {
            std::fs::write(&path, &whole[..cut]).unwrap();
            assert_eq!(Store::open(&d, false).unwrap().len(), 0, "a torn header at {cut}");
        }
        let _ = std::fs::remove_dir_all(&d);
    }
    #[test]
    fn damage_in_the_middle_is_an_error_and_damage_in_the_last_record_is_a_torn_write() {
        let d = dir("damage");
        let s = Store::open(&d, false).unwrap();
        for i in 0..3u8 { s.append(&vec![i; 50]).unwrap(); }
        drop(s);
        let path = d.join("blocks.log");
        let whole = std::fs::read(&path).unwrap();
        let rec = 8 + 50;
        let mut bad = whole.clone(); bad[8 + rec + 20] ^= 1;                   // inside record 2 of 3
        std::fs::write(&path, &bad).unwrap();
        assert!(Store::open(&d, false).err().unwrap().to_string().contains("damaged record"));
        let mut bad = whole.clone(); let last = whole.len() - 3; bad[last] ^= 1; // inside the last record
        std::fs::write(&path, &bad).unwrap();
        let s = Store::open(&d, false).unwrap();
        assert_eq!((s.len(), s.repaired), (2, rec as u64));
        std::fs::write(&path, b"not a zen log at all").unwrap();
        assert!(Store::open(&d, false).err().unwrap().to_string().contains("not a Zen block log"));
        let _ = std::fs::remove_dir_all(&d);
    }
    #[test]
    fn a_second_node_cannot_open_a_directory_in_use() {
        let d = dir("lock");
        let a = Store::open(&d, true).unwrap();
        assert!(Store::open(&d, true).err().unwrap().to_string().contains("in use"));
        drop(a);
        Store::open(&d, true).unwrap();
        let _ = std::fs::remove_dir_all(&d);
    }
}
