use crate::{Socket, msg_ptr, Message};
use libc::{c_int, c_void};

/// Sendable over a [Socket]`.
///
/// A type can implement this trait there is an especially efficient
/// implementation for sending it as a message over a zmq socket.
///
/// If the type needs to be directly passed to `Socket::send()`, but
/// the overhead of allocating a `Message` instance is not an issue,
/// `Into<Message>` should be implemented instead.
///
pub trait Sendable {
    fn send(self, socket: &Socket, flags: i32) -> crate::Result<()>;
}

/// Receivable over a [Socket]`.
///
/// Note that the `recv` function is unsafe. This is only because caller must ensure that the
/// data is well-formed, otherwise UB can occur.
pub trait Recvable: Sized {
    /// Receive. SAFETY: data must be the well-formed.
    /// i.e. if this implements [Sendable], the data must be the same as data sent by `send`.
    unsafe fn recv(socket: &Socket, flags: i32) -> crate::Result<Self>;
}

/// A type which is both [Sendable] and [Recvable]
pub trait SendableRecvable : Sendable + Recvable {}

macro_rules! sendable_into_message {
    ($T:ty) => {
        impl $crate::Sendable for $T {
            fn send(self, socket: &$crate::Socket, flags: i32) -> $crate::Result<()> {
                let msg = $crate::Message::from(self);
                msg.send(socket, flags)
            }
        }
    }
}

macro_rules! sendable_recvable_primitive {
    ($T:ty) => {
        impl $crate::Sendable for $T {
            fn send(self, socket: &$crate::Socket, flags: i32) -> $crate::Result<()> {
                socket.send(self.to_ne_bytes(), flags)
            }
        }

        impl $crate::Recvable for $T {
            unsafe fn recv(socket: &Socket, flags: i32) -> crate::Result<Self> {
                let mut bytes = [0u8; std::mem::size_of::<Self>()];
                let len = socket.recv_into(&mut bytes, flags)?;
                debug_assert_eq!(len, std::mem::size_of::<Self>());
                Ok(Self::from_ne_bytes(bytes))
            }
        }

        impl $crate::SendableRecvable for $T {}
    }
}

sendable_into_message!(Vec<u8>);
sendable_into_message!(Box<[u8]>);

sendable_recvable_primitive!(i8);
sendable_recvable_primitive!(i16);
sendable_recvable_primitive!(i32);
sendable_recvable_primitive!(i64);
sendable_recvable_primitive!(i128);
sendable_recvable_primitive!(isize);
sendable_recvable_primitive!(u8);
sendable_recvable_primitive!(u16);
sendable_recvable_primitive!(u32);
sendable_recvable_primitive!(u64);
sendable_recvable_primitive!(u128);
sendable_recvable_primitive!(usize);
sendable_recvable_primitive!(f32);
sendable_recvable_primitive!(f64);

impl Sendable for Message {
    fn send(mut self, socket: &Socket, flags: i32) -> crate::Result<()> {
        zmq_try!(unsafe { zmq_sys2::zmq_msg_send(msg_ptr(&mut self), socket.sock, flags as c_int) });
        Ok(())
    }
}

impl Sendable for () {
    fn send(self, socket: &Socket, flags: i32) -> crate::Result<()> {
        Message::new().send(socket, flags)
    }
}

impl Recvable for () {
    unsafe fn recv(socket: &Socket, flags: i32) -> crate::Result<Self> {
        let len = socket.recv_into(&mut [], flags)?;
        debug_assert_eq!(len, 0);
        Ok(())
    }
}

impl SendableRecvable for () {}

impl Sendable for bool {
    fn send(self, socket: &Socket, flags: i32) -> crate::Result<()> {
        if self {
            1u8.send(socket, flags)
        } else {
            0u8.send(socket, flags)
        }
    }
}

impl Recvable for bool {
    unsafe fn recv(socket: &Socket, flags: i32) -> crate::Result<Self> {
        let mut bytes = [0u8; 1];
        let len = socket.recv_into(&mut bytes, flags)?;
        debug_assert_eq!(len, 1);
        debug_assert!(bytes[0] == 0 || bytes[0] == 1);
        if bytes[0] == 0 {
            Ok(false)
        } else {
            Ok(true)
        }
    }
}

impl SendableRecvable for bool {}

impl<const L: usize> Sendable for [u8; L] {
    fn send(self, socket: &Socket, flags: i32) -> crate::Result<()> {
        zmq_try!(unsafe { zmq_sys2::zmq_send(socket.sock, &self as *const [u8] as *const c_void, L, flags as c_int) });
        Ok(())
    }
}

impl<'a> Sendable for &'a [u8] {
    fn send(self, socket: &Socket, flags: i32) -> crate::Result<()> {
        zmq_try!(unsafe { zmq_sys2::zmq_send(socket.sock, self as *const [u8] as *const c_void, self.len(), flags as c_int) });
        Ok(())
    }
}

impl<'a> Sendable for &'a Vec<u8> {
    fn send(self, socket: &Socket, flags: i32) -> crate::Result<()> {
        zmq_try!(unsafe { zmq_sys2::zmq_send(socket.sock, self.as_ptr() as *const c_void, self.len(), flags as c_int) });
        Ok(())
    }
}

impl<'a> Sendable for &'a str {
    fn send(self, socket: &Socket, flags: i32) -> crate::Result<()> {
        self.as_bytes().send(socket, flags)
    }
}

impl<'a> Sendable for &'a String {
    fn send(self, socket: &Socket, flags: i32) -> crate::Result<()> {
        self.as_bytes().send(socket, flags)
    }
}

impl<'a> Recvable for Vec<u8> {
    /// You should call [Socket::recv_bytes] instead of this or [Socket::recv_t] for `Vec<u8>`, as
    /// it is safe and this forwards to it.
    unsafe fn recv(socket: &Socket, flags: i32) -> crate::Result<Self> {
        socket.recv_bytes(flags)
    }
}

impl<'a> Recvable for String {
    /// Unsafe receive string. It's recommended to use [Socket::recv_string] and check unless you're
    /// absolutely sure that the data is valid UTF-8 (e.g. it was sent from a Rust string).
    unsafe fn recv(socket: &Socket, flags: i32) -> crate::Result<Self> {
        Ok(String::from_utf8_unchecked(socket.recv_bytes(flags)?))
    }
}