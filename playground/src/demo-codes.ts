// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
export const demoCodes = [
['Empty', ``],
['Factorial', `fn factorial(n) {
	if n <= 1 {
		1
	} else {
		n * factorial(n - 1)
	}
}

factorial(5)
`],
['Is even', `fn is_even(n) {
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
`],
['Product types', `fn f(x, y) {
	(x.1, x.1.0, y == x.1)
}

fn l2(v) {
	let sq = |x| x * x;
	sq(v.x) + sq(v.y)
}

fn id(x) {
	x
}

(id(1), id(true), id(|x, y| (y, x))(1, 1.3), l2({x:1, y:2}))
`],
['Sum types', `fn s_full(x) {
	match x {
		None => "no",
		Some(x) => f"hi {x}"
	}
}

fn s_def(x) {
	match x {
		None => "no",
		Some(x) => f"hi {x}",
		_ => "?"
	}
}

(s_full(Some(1)), s_full(None), s_def(Some(1)), s_def(Other))
`],
['Rust-style named types', `struct Point {
	x: int,
	y: int
}

fn dist2_gen(p) {
	p.x * p.x + p.y * p.y
}

fn dist2_point(p: Point) {
	p.x * p.x + p.y * p.y
}

enum Message {
	Quit,
	Move { x: int, y: int },
	Write(string),
	ChangeColor(int, int, int),
	Callback(() -> int)
}

fn energy_cost(m: Message) {
	match m {
		Quit => 0,
		Move { x, y } => x * x + y * y,
		Write(s) => string_len(s),
		ChangeColor(r, g, b) => r + g + b,
		Callback(f) => f()
	}
}

let dist_eq = dist2_gen({x: 3, y: 4}) == dist2_point(Point {x: 3, y: 4});
let e = energy_cost(Message::Write("hello"))
	+ energy_cost(Message::Move { x: 1, y: 2 })
	+ energy_cost(Message::ChangeColor(255, 0, 0))
	+ energy_cost(Message::Callback(|| 42));

(dist_eq, e)
`],
['Effects', `fn a(i, f, g) {
	if i > 0 {
	    b(i - 1, f, g); ()
	};
	f()
}

fn b(i, f, g) {
    a(i, f, g);
    g()
}

a(3, ||log("hi"), ||log("world"))
`],
['Quicksort', `fn quicksort(a, lo, hi) {
	if lo >= 0 and lo < hi {
		let p = partition(a, lo, hi);
		quicksort(a, lo, p - 1);
		quicksort(a, p + 1, hi)
	}
}

fn partition(a, lo, hi) {
	let pivot = a[hi];
	let mut i = lo;

	for j in lo..hi {
		if a[j] < pivot {
			swap(a, i, j);
			i += 1
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

let mut a = [5, 4, 11, 3, 2, 1, 0, 7];
quicksort(a, 0, len(a) - 1);
let mut b = [-1.3, 4.3, 2.3, -4.1];
quicksort(b, 0, len(b) - 1);
(a, b)
`],
['String', `let a = "hello";
let count = 3;
let mut text = f"{a} {count} worlds!";
string_push_str(text, " ...and more");
string_concat("He said: ", text)
`],
['Optional typing', `fn ty_let() {
	let a: int = 1;
	a
}

fn ty_expr() {
	(1: int)
}

fn ty_fn_arg(a: int, b: float) {
	(a + 1, b + 1)
}

fn ty_fn_ret(a) -> int {
	a
}

fn ty_fn_placeholders(a: (_, _)) {
	a.0 + a.1
}

fn ty_fn_arg_fn(f: () -> ()) {
	f()
}

((1: int), (1: float))
`],
['Type casting', `let a: int = 5;
let b = a as float;
let c = 5.7 as int;
(a, b, c)
`],
['Iterators',`fn sum2(seq) {
	let mut sum = 0;
	for i in seq {
		sum += i * i;
	};
	sum
}

fn range_sum2(start, end) {
	sum2(start..end)
}

fn range_inclusive_sum2(start, end) {
	sum2(start..=end)
}

(range_sum2(0, 5), range_inclusive_sum2(0, 5), sum2([1.0, 1.5, 2.0]))
`],
['Function pipe operator',
`[1, 2] |> array_concat([3, 4]) |> array_map(|x| x*x)`],
['Stack trace',
`fn f() -> float {
	1.0 / 0
}

fn g() {
	let x = || f();
	x()
}

g()
`]
] as const;