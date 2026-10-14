// The collector control's explicit "ba" collector, with a table of registrations.
static REGISTRATIONS: [&b01_model::Registration; 2] = [
    &b01_registration_beta::REGISTRATION,
    &b01_registration_alpha::REGISTRATION,
];

fn main() {
    b01_runner::main_with_registrations(&REGISTRATIONS);
}
