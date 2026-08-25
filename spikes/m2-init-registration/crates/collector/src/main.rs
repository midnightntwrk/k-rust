use std::any::TypeId;
use std::collections::HashSet;

fn main() {
    model::retain_for_collector();

    let mut descriptors = host::descriptors().collect::<Vec<_>>();
    descriptors.sort_by_key(|descriptor| descriptor.identity);
    assert_eq!(descriptors.len(), 3, "all configuration factories are linked");

    let unique_types = descriptors
        .iter()
        .map(|descriptor| (descriptor.type_key)())
        .collect::<HashSet<_>>();
    assert_eq!(unique_types.len(), 3, "each concrete Self type is distinct");

    for descriptor in descriptors {
        let concrete_type = if descriptor.identity.ends_with("::Alpha::init") {
            TypeId::of::<model::paired::Alpha>()
        } else if descriptor.identity.ends_with("::Beta::init") {
            TypeId::of::<model::paired::Beta>()
        } else if descriptor.identity.ends_with("::Gamma::init") {
            TypeId::of::<model::explicit::Gamma>()
        } else {
            panic!("unexpected descriptor identity: {}", descriptor.identity);
        };
        assert_eq!(
            (descriptor.type_key)(),
            concrete_type,
            "factory resolves the concrete authored configuration type",
        );
        let payload = (descriptor.payload)();
        println!(
            "{}|type={}|method={}",
            descriptor.identity,
            (descriptor.type_name)(),
            payload.method,
        );
    }
    println!("runtime_init_calls={}", model::runtime_init_calls());
    assert_eq!(model::runtime_init_calls(), 0);
}

