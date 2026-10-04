#![cfg(feature = "cli")]

use std::{
    fs,
    io::{BufRead, BufReader, Write},
    net::{SocketAddr, TcpStream},
    path::PathBuf,
    process::{Child, Command, Stdio},
    sync::mpsc,
    thread,
    time::Duration,
};

use serde_json::{Value, json};

struct Server {
    child: Child,
    root: PathBuf,
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn add_module_locates_written_unlicensed_injection() {
    let root = std::env::temp_dir().join(format!("k-rust-rpc-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let definition = root.join("definition.kore");
    fs::write(
        &definition,
        r#"[] module TEST
            sort SortA{} []
            sort SortB{} []
            symbol a{}() : SortA{} [constructor{}(), total{}()]
            symbol b{}() : SortB{} [constructor{}(), total{}()]
            symbol inj{From, To}(From) : To [sortInjection{}()]
        endmodule []"#,
    )
    .unwrap();
    let mut server = Server {
        child: Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kore-rpc", "--module", "TEST", "--server-port", "0"])
            .arg(&definition)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(),
        root,
    };
    let stderr = server.child.stderr.take().unwrap();
    let (send, receive) = mpsc::channel();
    thread::spawn(move || {
        for line in BufReader::new(stderr).lines() {
            let line = line.unwrap();
            if let Some(address) = line.strip_prefix("KORE JSON-RPC listening on ") {
                let _ = send.send(address.parse::<SocketAddr>().unwrap());
                break;
            }
        }
    });
    let address = receive.recv_timeout(Duration::from_secs(5)).unwrap();
    let mut connection = TcpStream::connect(address).unwrap();
    connection
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    connection
        .set_write_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    let request = json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "add-module",
        "params": {
            "module": r#"module BAD-AXIOM
                import TEST []
                axiom{} \rewrites{SortB{}}(
                    \and{SortB{}}(inj{SortA{}, SortB{}}(X:SortA{}), \top{SortB{}}()),
                    b{}()
                ) [label{}("dead-matched")]
                axiom{} \rewrites{SortB{}}(
                    \and{SortB{}}(b{}(), \top{SortB{}}()), b{}()
                ) [label{}("benign")]
                axiom{} \rewrites{SortB{}}(
                    \and{SortB{}}(b{}(), \top{SortB{}}()),
                    inj{SortA{}, SortB{}}(a{}())
                ) [label{}("written-rewrite")]
            endmodule []"#,
        },
    });
    writeln!(connection, "{request}").unwrap();
    let mut response = String::new();
    BufReader::new(connection).read_line(&mut response).unwrap();
    let response: Value = serde_json::from_str(&response).unwrap();
    assert_eq!(
        response["error"],
        json!({
            "code": 8,
            "message": "Invalid module",
            "data": {
                "error": "Unlicensed injection from SortA{} to SortB{} in axiom written-rewrite",
                "term": {
                    "format": "KORE",
                    "version": 1,
                    "term": {
                        "tag": "App",
                        "name": "inj",
                        "sorts": [
                            {"tag": "SortApp", "name": "SortA", "args": []},
                            {"tag": "SortApp", "name": "SortB", "args": []}
                        ],
                        "args": [{"tag": "App", "name": "a", "sorts": [], "args": []}]
                    }
                }
            },
        }),
        "{response:#}",
    );
}
