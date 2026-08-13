use crate::svdw::{SvdwMap, find_z};
use ark_ff::UniformRand;
use ark_vesta::VestaConfig;
use rand::thread_rng;

#[test]
fn test_gen() {
    let z = find_z::<VestaConfig>().unwrap();
    println!("z: {}", z);
}

#[test]
fn test_mapping() {
    let map = SvdwMap::<VestaConfig>::new();
    let mut rng = thread_rng();
    for i in 0..100 {
        let elem = ark_vesta::Fq::rand(&mut rng);
        let point = map.map(elem);
        assert!(point.is_on_curve(), "fail on {}", i);
    }
}
