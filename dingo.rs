trait Access {
    // has to have an associated type, but can be anything
    type Reader;

    fn read(&self) -> impl Future<Output = Self::Reader> + Send {
        async { loop {} }
    }
}

trait AccessDyn: Sync {}
impl Access for dyn AccessDyn {
    type Reader = ();
}

trait Stream {
    fn poll_next(s: &'static dyn AccessDyn);
}

// has to be a function in a trait impl, can't be a normal impl block or standalone fn
impl Stream for () {
    fn poll_next(s: &'static dyn AccessDyn) {
        // new async block is important
        is_dyn_send(&async {
            s.read().await;
        });
    }
}

fn is_dyn_send(_: &dyn Send) {}

fn main() {}
