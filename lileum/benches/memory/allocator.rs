//! Performant, thread-safe global allocator for tracking peak memory usage

use criterion::measurement::{Measurement, ValueFormatter};
use criterion::{Bencher, Throughput};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed};

static PEAK: AtomicUsize = AtomicUsize::new(0);
static CURRENT: AtomicUsize = AtomicUsize::new(0);
static BASELINE: AtomicUsize = AtomicUsize::new(0);

pub struct PeakTrackingAllocator;

unsafe impl GlobalAlloc for PeakTrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            // Relaxed/weakest is the minimal sufficient memory ordering required for this metric
            let current = CURRENT.fetch_add(layout.size(), Relaxed) + layout.size();
            let mut peak = PEAK.load(Relaxed);
            while current > peak {
                match PEAK.compare_exchange_weak(peak, current, Relaxed, Relaxed) {
                    Ok(_) => break,
                    Err(p) => peak = p,
                }
            }
        }

        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) };
        CURRENT.fetch_sub(layout.size(), Relaxed);
    }
}

impl PeakTrackingAllocator {
    // Reset peak high-water mark to the current baseline so subsequent
    // allocations are measured relative to this
    pub fn reset_peak(&self) {
        let current = CURRENT.load(Relaxed);
        BASELINE.store(current, Relaxed);
        PEAK.store(current, Relaxed);
    }

    pub fn peak_bytes(&self) -> usize {
        PEAK.load(Relaxed).saturating_sub(BASELINE.load(Relaxed))
    }
}

// Custom Criterion measurement for the peak live heap (in bytes) reached
// by PeakTrackingAllocator during the benchmarked operation
pub struct PeakMemory;

// Benchmark the peak live-heap bytes of memory reached while running f,
// recorded as a Criterion sample value
pub fn bench_memory(b: &mut Bencher<'_, PeakMemory>, mut f: impl FnMut()) {
    b.iter_custom(|iters| {
        let mut peak = 0usize;

        for _ in 0..iters {
            super::ALLOCATOR.reset_peak();
            f();
            peak = peak.max(super::ALLOCATOR.peak_bytes());
        }

        // Workaround: peak memory is deterministic, which makes Criterion's report
        // plots panic. Add a few bytes jitter (~3 orders of magnitude below the MiB
        // display resolution) so sample variance is non-zero and the plots render.
        static SAMPLE: AtomicU64 = AtomicU64::new(0);
        let jitter = SAMPLE.fetch_add(1, Relaxed) & 0x3F; // 0..=63 bytes

        // Criterion divides the returned value by iters to get the per-iteration
        // estimate. Since peak memory does not scale with iteration count, scale by
        // iters to recover the true per-iteration peak.
        (peak as u64) * iters + jitter
    });
}

impl Measurement for PeakMemory {
    type Intermediate = usize;
    type Value = u64;

    fn start(&self) -> Self::Intermediate {
        super::ALLOCATOR.reset_peak();
        super::ALLOCATOR.peak_bytes()
    }

    fn end(&self, _i: Self::Intermediate) -> Self::Value {
        super::ALLOCATOR.peak_bytes() as u64
    }

    fn add(&self, v1: &Self::Value, v2: &Self::Value) -> Self::Value {
        v1 + v2
    }

    fn zero(&self) -> Self::Value {
        0
    }

    fn to_f64(&self, value: &Self::Value) -> f64 {
        *value as f64
    }

    fn formatter(&self) -> &dyn ValueFormatter {
        &ByteFormatter
    }
}

struct ByteFormatter;

impl ValueFormatter for ByteFormatter {
    fn scale_values(&self, typical: f64, values: &mut [f64]) -> &'static str {
        let (factor, unit) = if typical < (1u64 << 10) as f64 {
            (1.0, "B")
        } else if typical < (1u64 << 20) as f64 {
            (1.0 / (1u64 << 10) as f64, "KiB")
        } else if typical < (1u64 << 30) as f64 {
            (1.0 / (1u64 << 20) as f64, "MiB")
        } else {
            (1.0 / (1u64 << 30) as f64, "GiB")
        };

        for val in values.iter_mut() {
            *val *= factor;
        }

        unit
    }

    fn scale_throughputs(
        &self,
        typical: f64,
        _throughput: &Throughput,
        values: &mut [f64],
    ) -> &'static str {
        // Peak memory is not a throughput; fall back to plain byte scaling.
        self.scale_values(typical, values)
    }

    fn scale_for_machines(&self, _values: &mut [f64]) -> &'static str {
        "bytes"
    }
}
