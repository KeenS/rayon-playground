#![allow(dead_code)]
#![allow(unused_macros)]
#![feature(test)]

extern crate rand;
extern crate rayon;
extern crate test;
use test::Bencher;

use rand::Rng;

fn main() {
    use rayon::prelude::*;
    let vec = vec![1, 2, 3, 4, 5, 6];
    let max = vec.par_iter().max();
    assert_eq!(max, Some(&6));

    let vec = vec![1, 2, 3, 4, 5, 6];
    let (min, max) = min_max(&vec);
    assert_eq!(min, Some(&1));
    assert_eq!(max, Some(&6));

    let vec = vec![1, 2, 3, 4, 5, 6];
    let (min, max) = min_max_rayon(&vec);
    assert_eq!(min, Some(&1));
    assert_eq!(max, Some(&6));
}

fn min_max<T: Ord>(v: &[T]) -> (Option<&T>, Option<&T>) {
    if v.is_empty() {
        return (None, None);
    } else {
        let (min, max) = min_max_(v);
        (Some(min), Some(max))
    }
}

fn min_max_<T: Ord>(v: &[T]) -> (&T, &T) {
    use std::cmp;
    debug_assert!(0 < v.len());
    let mut iter = v.iter();
    let mut min;
    let mut max;
    if v.len() % 2 == 0 {
        min = iter.next().unwrap();
        max = iter.next().unwrap();
    } else {
        min = iter.next().unwrap();
        max = min;
    }
    while let Some(a) = iter.next() {
        if let Some(b) = iter.next() {
            let (small, large) = if a < b { (a, b) } else { (b, a) };
            min = cmp::min(min, small);
            max = cmp::max(max, large);
        } else {
            break;
        }
    }
    (min, max)
}

macro_rules! gen_min_max_rayon {
    ($threshold: expr) => {
        fn min_max_rayon<T: Ord + Send + Sync>(v: &[T]) -> (Option<&T>, Option<&T>) {
            match v.len() {
                0 => (None, None),
                1 => (Some(&v[0]), Some(&v[0])),
                _ => {
                    let (min, max) = min_max_rayon_(v);
                    (Some(min), Some(max))
                }
            }
        }
        fn min_max_rayon_<T: Ord + Send + Sync>(v: &[T]) -> (&T, &T) {
            use std::cmp;
            debug_assert!(1 < v.len());

            if v.len() <= $threshold {
                min_max_(v)
            } else {
                fn doit<T: Ord + Send + Sync>(v: &[T]) -> (&T, &T) {
                    let mid = match v.len() % 4 {
                        0 => v.len() / 2,
                        2 => v.len() / 2 + 2,
                        _ => unreachable!(),
                    };
                    let ((min1, max1), (min2, max2)) =
                    // ここで `rayon::join` を用いている
                        rayon::join(|| min_max_rayon_(&v[..mid]), || min_max_rayon_(&v[mid..]));
                    (cmp::min(min1, min2), cmp::max(max1, max2))
                }
                if v.len() % 2 == 1 {
                    let t = &v[0];
                    let v = &v[1..];
                    let (min, max) = doit(v);
                    (cmp::min(t, min), cmp::max(t, max))
                } else {
                    doit(v)
                }
            }
        }
    }
}

//for main
gen_min_max_rayon!(8192);

fn random_vec(n: usize) -> Vec<i32> {
    let mut rng = rand::thread_rng();
    (0..n).into_iter().map(|_| rng.gen::<i32>()).collect()
}

macro_rules! gen_benches {
    ($($name: ident => $n: expr),*) => {
        mod bench_min_and_max {
            pub use super::*;
            $(mod $name {
                use super::*;
                #[bench]
                fn run(b: &mut Bencher) {
                    let v = random_vec($n);
                    b.iter(|| (v.iter().min(), v.iter().max()))
                }
            })*
        }
        mod bench_min_and_max_rayon {
            pub use super::*;
            $(mod $name {
                use super::*;
                #[bench]
                fn run(b: &mut Bencher) {
                    use rayon::prelude::*;
                    let v = random_vec($n);
                    b.iter(|| (v.par_iter().min(), v.par_iter().max()))
                }
            })*
        }
        mod bench_min_max {
            pub use super::*;
            $(mod $name {
                use super::*;
                #[bench]
                fn run(b: &mut Bencher) {
                    let v = random_vec($n);
                    b.iter(|| min_max(&v))
                }
            })*
        }
    }
}

macro_rules! gen_bench_rayon_min_max {
    ($($name: ident => $n: expr),*) => {
        mod bench_min_max_rayon {
            pub use super::*;
            $(
                mod $name {
                    use super::*;
                    #[bench]
                    fn run(b: &mut Bencher) {
                        let v = random_vec($n);
                        b.iter(|| min_max_rayon(&v))
                    }
                }
            )*
        }
    }
}

macro_rules! with_thresholds {
    ([$($name: ident => $threshold: expr),*], $body: item) => {
        $(mod $name {
            pub use super::*;
            gen_min_max_rayon!($threshold);
            $body
        })*
    }
}

gen_benches! {
    n0000002 => 0000002,
    n0000004 => 0000004,
    n0000008 => 0000008,
    n0000016 => 0000016,
    n0000032 => 0000032,
    n0000064 => 0000064,
    n0000128 => 0000128,
    n0000256 => 0000256,
    n0000512 => 0000512,
    n0001024 => 0001024,
    n0002048 => 0002048,
    n0004096 => 0004096,
    n0008192 => 0008192,
    n0016384 => 0016384,
    n0032768 => 0032768,
    n0065536 => 0065536,
    n0131072 => 0131072,
    n0262144 => 0262144,
    n0524288 => 0524288,
    n1048576 => 1048576
}
with_thresholds!([
    th0000001 => 0000001,
    th0000002 => 0000002,
    th0000004 => 0000004,
    th0000008 => 0000008,
    th0000016 => 0000016,
    th0000032 => 0000032,
    th0000064 => 0000064,
    th0000128 => 0000128,
    th0000256 => 0000256,
    th0000512 => 0000512,
    th0001024 => 0001024,
    th0002048 => 0002048,
    th0004096 => 0004096,
    th0008192 => 0008192,
    th0016384 => 0016384,
    th0032768 => 0032768,
    th0065536 => 0065536,
    th0131072 => 0131072,
    th0262144 => 0262144,
    th0524288 => 0524288,
    th1048576 => 1048576
],
                 gen_bench_rayon_min_max!{
                     n0000002 => 0000002,
                     n0000004 => 0000004,
                     n0000008 => 0000008,
                     n0000016 => 0000016,
                     n0000032 => 0000032,
                     n0000064 => 0000064,
                     n0000128 => 0000128,
                     n0000256 => 0000256,
                     n0000512 => 0000512,
                     n0001024 => 0001024,
                     n0002048 => 0002048,
                     n0004096 => 0004096,
                     n0008192 => 0008192,
                     n0016384 => 0016384,
                     n0032768 => 0032768,
                     n0065536 => 0065536,
                     n0131072 => 0131072,
                     n0262144 => 0262144,
                     n0524288 => 0524288,
                     n1048576 => 1048576
                 });

fn quick_sort<T: PartialOrd + Send>(v: &mut [T]) {
    if v.len() > 1 {
        let mid = partition(v);
        let (lo, hi) = v.split_at_mut(mid);
        rayon::join(|| quick_sort(lo), || quick_sort(hi));
    }
}

// Partition rearranges all items `<=` to the pivot
// item (arbitrary selected to be the last item in the slice)
// to the first half of the slice. It then returns the
// "dividing point" where the pivot is placed.
fn partition<T: PartialOrd + Send>(v: &mut [T]) -> usize {
    let pivot = v.len() - 1;
    let mut i = 0;
    for j in 0..pivot {
        if v[j] <= v[pivot] {
            v.swap(i, j);
            i += 1;
        }
    }
    v.swap(i, pivot);
    i
}

fn max<T: PartialOrd + Send + Sync>(v: &[T]) -> &T {
    if v.len() > 1 {
        let mid = v.len() / 2;
        let lo = &v[0..mid];
        let hi = &v[mid..];
        let (m1, m2) = rayon::join(|| max(lo), || max(hi));
        if m1 > m2 {
            m1
        } else {
            m2
        }
    } else {
        &v[0]
    }
}

fn msc<T: PartialOrd + Send + Sync>(v: &[T]) -> usize {
    v.iter()
        .enumerate()
        .map(|(n, t)| scount(t, &v[n..]))
        .max()
        .unwrap()
}

fn scount<T: PartialOrd + Send + Sync>(t: &T, v: &[T]) -> usize {
    v.iter().filter(|s| t < s).count()
}

fn msc_divide<T: PartialOrd + Send + Sync>(v: &[T]) -> usize {
    table(v).into_iter().map(|(_, n)| n).max().unwrap()
}

fn msc_rayon<T: PartialOrd + Send + Sync>(v: &[T]) -> usize {
    table_rayon(v).into_iter().map(|(_, n)| n).max().unwrap()
}

fn msc_rayon2<T: PartialOrd + Send + Sync>(v: &[T]) -> usize {
    let mut into = Vec::new();
    table_rayon2(v, &mut into);
    into.into_iter().map(|(_, n)| n).max().unwrap()
}

fn table<T: PartialOrd + Send + Sync>(v: &[T]) -> Vec<(&T, usize)> {
    if v.len() == 1 {
        vec![(&v[0], 0)]
    } else {
        let mid = v.len() / 2;
        let xs = &v[0..mid];
        let ys = &v[mid..];
        let xs = table(xs);
        let ys = table(ys);
        join(&xs, &ys)
    }
}

fn table_rayon<T: PartialOrd + Send + Sync>(v: &[T]) -> Vec<(&T, usize)> {
    if v.len() == 1 {
        vec![(&v[0], 0)]
    } else {
        let mid = v.len() / 2;
        let xs = &v[0..mid];
        let ys = &v[mid..];
        let (xs, ys) = rayon::join(|| table_rayon(xs), || table_rayon(ys));
        join(&xs, &ys)
    }
}

fn table_rayon2<'a, T: PartialOrd + Send + Sync>(v: &'a [T], into: &mut Vec<(&'a T, usize)>) {
    if v.len() == 1 {
        into.push((&v[0], 0))
    } else {
        let mid = v.len() / 2;
        let xs = &v[0..mid];
        let ys = &v[mid..];
        let mut xs_into = Vec::new();
        let mut ys_into = Vec::new();
        rayon::join(
            || table_rayon2(xs, &mut xs_into),
            || table_rayon2(ys, &mut ys_into),
        );
        join2(&xs_into, &ys_into, into)
    }
}

fn join<'a, 'v, T: PartialOrd + Send + Sync>(
    mut xs: &'a [(&'v T, usize)],
    mut ys: &'a [(&'v T, usize)],
) -> Vec<(&'v T, usize)> {
    let mut v = Vec::new();
    loop {
        if ys.is_empty() {
            v.extend(xs);
            return v;
        } else if xs.is_empty() {
            v.extend(ys);
            return v;
        } else {
            let xt = &xs[0];
            let yt = &ys[0];
            if xt.0 < yt.0 {
                v.push((xt.0, xt.1 + ys.len()));
                xs = &xs[1..];
            } else {
                v.push(yt.clone());
                ys = &ys[1..];
            }
        }
    }
}

fn join2<'a, 'v, T: PartialOrd + Send + Sync>(
    mut xs: &'a [(&'v T, usize)],
    mut ys: &'a [(&'v T, usize)],
    v: &mut Vec<(&'v T, usize)>,
) {
    loop {
        if ys.is_empty() {
            v.extend(xs);
            return;
        } else if xs.is_empty() {
            v.extend(ys);
            return;
        } else {
            let xt = &xs[0];
            let yt = &ys[0];
            if xt.0 < yt.0 {
                v.push((xt.0, xt.1 + ys.len()));
                xs = &xs[1..];
            } else {
                v.push(yt.clone());
                ys = &ys[1..];
            }
        }
    }
}

#[test]
fn msc_and_ms_rayon_returns_the_same_result() {
    let v = "GENERATING".chars().collect::<Vec<_>>();
    let m1 = msc(&v);
    let m2 = msc_rayon(&v);
    assert_eq!(m1, m2);
}

macro_rules! bench_mscs {
    ($name:ident, $n:expr) => {
        mod $name {
            use super::*;
            #[bench]
            fn bench_msc_rayon(b: &mut Bencher) {
                let v = vec![1; $n];
                b.iter(|| msc_rayon(&v))
            }

            #[bench]
            fn bench_msc_rayon2(b: &mut Bencher) {
                let v = vec![1; $n];
                b.iter(|| msc_rayon2(&v))
            }

            #[bench]
            fn bench_msc_divide(b: &mut Bencher) {
                let v = vec![1; $n];
                b.iter(|| msc_divide(&v))
            }
        }
    };
}

// bench_mscs!(n0008, 0008);
