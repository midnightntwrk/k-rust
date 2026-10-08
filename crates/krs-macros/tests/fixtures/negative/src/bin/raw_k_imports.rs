use renamed_krs as k;

k::raw_k!("rule a => b imports INT"); //~ ERROR `raw_k!` holds exactly one sentence, with no `module`, `endmodule` or `imports`; `imports` starts another

fn main() {}
