// spikes/BL-003/browser-control/collector-ab-explicit.rs with a table of registrations.
static REGISTRATIONS: [&b01_model::Registration; 2] = [
    &b01_registration_alpha::REGISTRATION,
    &b01_registration_beta::REGISTRATION,
];

fn main() {
    b01_runner::main_with_registrations(&REGISTRATIONS);
}
