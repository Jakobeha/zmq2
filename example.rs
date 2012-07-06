use std;
use zmq;

import result::{ok, err};

import zmq::{context, socket, socket_util, to_str};

fn new_server(ctx: zmq::context, ch: comm::chan<()>) {
    // FIXME: https://github.com/mozilla/rust/issues/2329.
    let socket = ctx.socket(zmq::REP);
    if socket.is_err() { fail socket.get_err().to_str() };
    let socket = result::unwrap(socket);

    alt socket.bind("tcp://127.0.0.1:3456") {
      ok(()) { }
      err(e) { fail e.to_str(); }
    }

    let msg = alt socket.recv_str(0) {
      ok(s) { copy s }
      err(e) { fail e.to_str() }
    };

    io::println(#fmt("received %s", msg));

    alt socket.send_str(#fmt("hello %s", msg), 0) {
      ok(()) { }
      err(e) { fail e.to_str(); }
    }

    // Let the main thread know we're done.
    comm::send(ch, ());
}

fn new_client(ctx: zmq::context) {
    io::println("starting client");

    // FIXME: https://github.com/mozilla/rust/issues/2329.
    let socket = ctx.socket(zmq::REQ);
    if socket.is_err() { fail socket.get_err().to_str() };
    let socket = result::unwrap(socket);

    alt socket.set_hwm(10u64) {
      ok(()) { }
      err(e) { fail e.to_str(); }
    };

    alt socket.get_hwm() {
      ok(hwm) { io::println(#fmt("hwm: %s", u64::str(hwm))); }
      err(e) { fail e.to_str(); }
    }

    alt socket.set_identity("identity") {
      ok(()) { }
      err(e) { fail e.to_str(); }
    };

    alt socket.get_identity() {
      ok(identity) {
          io::println(#fmt("identity: %s", str::from_bytes(copy identity)))
      }
      err(e) { fail e.to_str() }
    };

    io::println("client connecting to server");

    alt socket.connect("tcp://127.0.0.1:3456") {
      ok(()) { }
      err(e) { fail e.to_str() }
    };

    alt socket.send_str("foo", 0) {
      ok(()) { }
      err(e) { fail e.to_str(); }
    }

    alt socket.recv_str(0) {
      ok(s) { io::println(s); }
      err(e) { fail e.to_str(); }
    }
}

fn main() {
    let (major, minor, patch) = zmq::version();

    io::println(#fmt("version: %d %d %d", major, minor, patch));

    let ctx = alt zmq::init(1) {
      ok(ctx) { ctx }
      err(e) { fail e.to_str() }
    };

    // We need to start the server in a separate scheduler as it blocks.
    let po = comm::port();
    let ch = comm::chan(po);
    do task::spawn_sched(task::single_threaded) { new_server(ctx, ch) }

    new_client(ctx);

    // Wait for the server to shut down.
    comm::recv(po);

    alt ctx.term() {
      ok(()) { }
      err(e) { fail e.to_str() }
    };
}