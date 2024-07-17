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
id(1)
`
];