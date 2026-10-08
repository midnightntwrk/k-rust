use renamed_krs as k;

k::raw_k!("rule a => b rule b => c"); //~ ERROR `raw_k!` holds exactly one sentence, with no `module`, `endmodule` or `imports`; `rule` starts another

fn main() {}
