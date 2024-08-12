mod common;

use test_log::test;

use common::run;
use painturscript::value::Value;

#[test]
fn quicksort() {
    assert_eq!(
        run(r#"fn quicksort(a, lo, hi) {
            if lo >= hi or lo < 0 {
                ()
            } else {
                let p = partition(a, lo, hi);
                quicksort(a, lo, p - 1);
                quicksort(a, p + 1, hi)
            }
        }

        fn partition(a, lo, hi) {
            let pivot = a[hi];
            var i = lo;

            for j in lo..hi {
                if a[j] < pivot {
                    let temp = a[i];
                    a[i] = a[j];
                    a[j] = temp;
                    i = i + 1
                } else {
                    ()
                }
            };

            let temp = a[i];
            a[i] = a[hi];
            a[hi] = temp;

            i
        }

        var a = [5, 4, 11, 3, 2, 1, 0, 7];
        quicksort(a, 0, array_len(a) - 1);
        a"#),
        int_a![0, 1, 2, 3, 4, 5, 7, 11],
    );
}
