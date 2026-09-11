use legitimacy::trajectory::codex_exec_v0::codex_exec_sanitizer_compiled_attestation_v0;
use std::fs::File;
use std::io::{Read, Write};
use std::os::unix::fs::MetadataExt;
use std::process::ExitCode;

const MAGIC: &[u8] = b"legitimacy.selected-authority.rlib-probe\0";
const MAX_RLIB_BYTES: u64 = 1024 * 1024 * 1024;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("selected rlib probe: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), &'static str> {
    let arguments = std::env::args().collect::<Vec<_>>();
    let [_, flag, rlib_path] = arguments.as_slice() else {
        return Err("argv shape");
    };
    if flag != "--rlib" || !rlib_path.starts_with('/') || rlib_path.contains('\0') {
        return Err("rlib argument");
    }
    let mut rlib = File::open(rlib_path).map_err(|_| "rlib open")?;
    let metadata = rlib.metadata().map_err(|_| "rlib metadata")?;
    if !metadata.is_file() || metadata.len() > MAX_RLIB_BYTES {
        return Err("rlib identity");
    }
    let mut hasher = Sha256::new();
    let mut buffer = [0; 64 * 1024];
    let mut observed = 0u64;
    loop {
        let count = rlib.read(&mut buffer).map_err(|_| "rlib read")?;
        if count == 0 {
            break;
        }
        observed = observed
            .checked_add(u64::try_from(count).map_err(|_| "rlib length")?)
            .ok_or("rlib length")?;
        if observed > MAX_RLIB_BYTES {
            return Err("rlib cap");
        }
        hasher.update(&buffer[..count])?;
    }
    if observed != metadata.len() {
        return Err("rlib changed");
    }
    let rlib_digest = hasher.finalize()?;

    let attestation = codex_exec_sanitizer_compiled_attestation_v0();
    if attestation.components().len() > 64 {
        return Err("component cap");
    }
    let mut record = Vec::new();
    record.extend_from_slice(MAGIC);
    record.extend_from_slice(&1u16.to_be_bytes());
    frame(&mut record, attestation.schema_identity().as_bytes())?;
    record.extend_from_slice(&attestation.schema_version().to_be_bytes());
    record.extend_from_slice(
        &u32::try_from(attestation.components().len())
            .map_err(|_| "component count")?
            .to_be_bytes(),
    );
    for (index, component) in attestation.components().iter().enumerate() {
        record.extend_from_slice(
            &u32::try_from(index)
                .map_err(|_| "component index")?
                .to_be_bytes(),
        );
        frame(&mut record, component.component_key().as_bytes())?;
        record.extend_from_slice(&component.byte_length().to_be_bytes());
        record.extend_from_slice(&component.sha256());
    }
    frame(&mut record, attestation.aggregate().identity.as_bytes())?;
    frame(&mut record, attestation.aggregate().version.as_bytes())?;
    frame(&mut record, attestation.aggregate().hash.as_bytes())?;
    frame(&mut record, rlib_path.as_bytes())?;
    record.extend_from_slice(&metadata.dev().to_be_bytes());
    record.extend_from_slice(&metadata.ino().to_be_bytes());
    record.extend_from_slice(&metadata.len().to_be_bytes());
    record.extend_from_slice(&rlib_digest);
    std::io::stdout()
        .lock()
        .write_all(&record)
        .map_err(|_| "stdout write")
}

fn frame(output: &mut Vec<u8>, bytes: &[u8]) -> Result<(), &'static str> {
    output.extend_from_slice(
        &u64::try_from(bytes.len())
            .map_err(|_| "frame length")?
            .to_be_bytes(),
    );
    output.extend_from_slice(bytes);
    Ok(())
}

struct Sha256 {
    state: [u32; 8],
    buffer: [u8; 64],
    buffered: usize,
    byte_len: u64,
}

impl Sha256 {
    fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            buffer: [0; 64],
            buffered: 0,
            byte_len: 0,
        }
    }

    fn update(&mut self, mut bytes: &[u8]) -> Result<(), &'static str> {
        self.byte_len = self
            .byte_len
            .checked_add(u64::try_from(bytes.len()).map_err(|_| "SHA-256 length")?)
            .ok_or("SHA-256 length")?;
        if self.buffered != 0 {
            let count = (64 - self.buffered).min(bytes.len());
            self.buffer[self.buffered..self.buffered + count].copy_from_slice(&bytes[..count]);
            self.buffered += count;
            bytes = &bytes[count..];
            if self.buffered == 64 {
                let block = self.buffer;
                self.compress(&block);
                self.buffered = 0;
            }
        }
        while bytes.len() >= 64 {
            let block: &[u8; 64] = bytes[..64].try_into().map_err(|_| "SHA-256 block")?;
            self.compress(block);
            bytes = &bytes[64..];
        }
        self.buffer[..bytes.len()].copy_from_slice(bytes);
        self.buffered = bytes.len();
        Ok(())
    }

    fn finalize(mut self) -> Result<[u8; 32], &'static str> {
        let bit_len = self.byte_len.checked_mul(8).ok_or("SHA-256 length")?;
        self.buffer[self.buffered] = 0x80;
        self.buffered += 1;
        if self.buffered > 56 {
            self.buffer[self.buffered..].fill(0);
            let block = self.buffer;
            self.compress(&block);
            self.buffer = [0; 64];
        } else {
            self.buffer[self.buffered..56].fill(0);
        }
        self.buffer[56..].copy_from_slice(&bit_len.to_be_bytes());
        let block = self.buffer;
        self.compress(&block);
        let mut output = [0; 32];
        for (chunk, value) in output.chunks_exact_mut(4).zip(self.state) {
            chunk.copy_from_slice(&value.to_be_bytes());
        }
        Ok(output)
    }

    fn compress(&mut self, block: &[u8; 64]) {
        const K: [u32; 64] = [
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
            0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
            0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
            0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
            0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
            0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
            0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
            0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
            0xc67178f2,
        ];
        let mut schedule = [0u32; 64];
        for (word, bytes) in schedule.iter_mut().zip(block.chunks_exact(4)) {
            *word = u32::from_be_bytes(bytes.try_into().expect("four-byte word"));
        }
        for index in 16..64 {
            let s0 = schedule[index - 15].rotate_right(7)
                ^ schedule[index - 15].rotate_right(18)
                ^ (schedule[index - 15] >> 3);
            let s1 = schedule[index - 2].rotate_right(17)
                ^ schedule[index - 2].rotate_right(19)
                ^ (schedule[index - 2] >> 10);
            schedule[index] = schedule[index - 16]
                .wrapping_add(s0)
                .wrapping_add(schedule[index - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = self.state;
        for index in 0..64 {
            let sum1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choice = (e & f) ^ ((!e) & g);
            let temporary1 = h
                .wrapping_add(sum1)
                .wrapping_add(choice)
                .wrapping_add(K[index])
                .wrapping_add(schedule[index]);
            let sum0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let temporary2 = sum0.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temporary1);
            d = c;
            c = b;
            b = a;
            a = temporary1.wrapping_add(temporary2);
        }
        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
        self.state[5] = self.state[5].wrapping_add(f);
        self.state[6] = self.state[6].wrapping_add(g);
        self.state[7] = self.state[7].wrapping_add(h);
    }
}
