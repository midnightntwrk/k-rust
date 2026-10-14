fn main() {
    let declared = b02_registrations::force_link();
    let mut names = b02_registry::names();
    names.sort_unstable();
    println!("declared={declared} registrations={} names={names:?}", names.len());
}
