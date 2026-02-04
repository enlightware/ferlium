(function () {
	if (typeof window === "undefined" || !window.hljs) {
		return;
	}

	function ferlium(hljs) {
		return {
			name: "Ferlium",
			aliases: ["ferlium"],
			keywords: {
				keyword: "fn impl struct enum use let mut return if else match for in as and or not",
				literal: "true false",
				type: "int string bool float",
				built_in: "_",
			},
			contains: [
				hljs.C_LINE_COMMENT_MODE,
				hljs.C_BLOCK_COMMENT_MODE,
				{
					className: "string",
					begin: /f?"/,
					end: /"/,
					contains: [hljs.BACKSLASH_ESCAPE],
				},
				{
					className: "number",
					begin: /\b\d+\b/,
				},
				{
					className: "operator",
					begin: /\.\.=?|=>|\|>|\+=|-=|\*=|\/=|==|!=|>=|<=|=|>|<|\+|-|\*|\/|%|\||&|!/,
				},
				{
					className: "punctuation",
					begin: /[(){}\[\],;:.]/,
				},
			],
		};
	}

	function rehighlightFerliumBlocks(hljs) {
		const blocks = document.querySelectorAll("pre code.language-ferlium, pre code.ferlium");
		blocks.forEach((el) => {
			// Avoid double-highlighting if mdBook already did something weird
			// (optional, but harmless)
			if (el.dataset.ferliumHighlighted === "1") return;

			if (typeof hljs.highlightElement === "function") {
				hljs.highlightElement(el);
			} else if (typeof hljs.highlightBlock === "function") {
				hljs.highlightBlock(el);
			} else if (typeof hljs.highlight === "function") {
				// Very old API fallback
				const res = hljs.highlight(el.textContent, { language: "ferlium", ignoreIllegals: true });
				el.innerHTML = res.value;
				el.classList.add("hljs");
			}

			el.dataset.ferliumHighlighted = "1";
		});
	}

	function registerAndHighlight() {
		const hljs = window.hljs;
		if (!hljs || typeof hljs.registerLanguage !== "function") return false;

		// Register only once
		if (!window.__ferlium_registered) {
			hljs.registerLanguage("ferlium", ferlium);
			window.__ferlium_registered = true;
		}

		// Highlight just Ferlium blocks
		if (typeof document !== "undefined") {
			rehighlightFerliumBlocks(hljs);
		}

		return true;
	}

	// Try now; if hljs isn't present yet, retry briefly (load-order safe)
	if (!registerAndHighlight()) {
		let tries = 0;
		const t = setInterval(() => {
			tries += 1;
			if (registerAndHighlight() || tries > 50) clearInterval(t);
		}, 50);
	}
})();
