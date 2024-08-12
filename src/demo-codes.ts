export const demoCodes = [
	``,
	`fn factorial(n) {
	if n <= 1 {
		1
	} else {
		n * factorial(n - 1)
	}
}

factorial(5)
`,
	`fn is_even(n) {
	if n == 0 {
		true
	} else {
		is_odd(n - 1)
	}
}

fn is_odd(n) {
	if n == 0 {
		false
	} else {
		is_even(n - 1)
	}
}

is_even(10)
`,
	`let f = |x, y| (x.1, x.1.0, y == x.1);
let id = |x| x;
(id(1), id(true), id(|x, y| (y, x)))
`,
	`let a = [];
(array_concat(a, [1]), array_concat(a, [true]))
`,
`fn quicksort(a, lo, hi) {
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
			swap(a, i, j);
			i = i + 1
		} else {
			()
		}
	};

	swap(a, i, hi);

	i
}

fn swap(a, i, j) {
	let temp = a[i];
	a[i] = a[j];
	a[j] = temp
}

var a = [5, 4, 11, 3, 2, 1, 0, 7];
quicksort(a, 0, array_len(a) - 1);
a
`
];