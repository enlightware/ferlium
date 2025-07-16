#!/usr/bin/env node

import { readFileSync, readdirSync, statSync } from 'fs';
import { join } from 'path';
import { pathToFileURL } from 'url';

// Get the grammar file path and options from command line arguments
const grammarPath = process.argv[2];
const verboseMode = process.argv.includes('--verbose') || process.argv.includes('-v');
const errorsOnly = process.argv.includes('--errors') || process.argv.includes('-e');

if (!grammarPath) {
  console.error('Usage: node extract-test-grammar.js <grammar.js> [--verbose|-v] [--errors|-e]');
  console.error('  --verbose, -v  Show detailed parse trees and full analysis');
  console.error('  --errors, -e   Only show errors, skip successful parses');
  process.exit(1);
}

// Import the generated parser
const grammarModule = await import(pathToFileURL(grammarPath));
const parser = grammarModule.parser;

// Function to extract code snippets from Rust test files
function extractCodeSnippets(content) {
  const snippets = [];  // Comprehensive patterns to match all combinations of indoc and string literal types
  const patterns = [
    // Regular run() calls without indoc
    { regex: /run\s*\(\s*"([^"\\]*(\\.[^"\\]*)*)"\s*\)/g, isIndoc: false, stringType: 'regular' },
    { regex: /run\s*\(\s*r"([^"\\]*(\\.[^"\\]*)*)"\s*\)/g, isIndoc: false, stringType: 'raw' },
    { regex: /run\s*\(\s*r#"([^"]*(?:"(?!#)[^"]*)*)"#\s*\)/g, isIndoc: false, stringType: 'raw_hash' },

    // indoc! calls with different string literal types
    { regex: /run\s*\(\s*indoc!\s*\{\s*"([^"\\]*(\\.[^"\\]*)*)"\s*\}\s*\)/g, isIndoc: true, stringType: 'regular' },
    { regex: /run\s*\(\s*indoc!\s*\{\s*r"([^"\\]*(\\.[^"\\]*)*)"\s*\}\s*\)/g, isIndoc: true, stringType: 'raw' },
    { regex: /run\s*\(\s*indoc!\s*\{\s*r#"([^"]*(?:"(?!#)[^"]*)*)"#\s*\}\s*\)/g, isIndoc: true, stringType: 'raw_hash' },

    // let mod_src = patterns without indoc
    { regex: /let\s+mod_src\s*=\s*"([^"\\]*(\\.[^"\\]*)*)"\s*;/g, isIndoc: false, stringType: 'regular' },
    { regex: /let\s+mod_src\s*=\s*r"([^"\\]*(\\.[^"\\]*)*)"\s*;/g, isIndoc: false, stringType: 'raw' },
    { regex: /let\s+mod_src\s*=\s*r#"([^"]*(?:"(?!#)[^"]*)*)"#\s*;/g, isIndoc: false, stringType: 'raw_hash' },

    // let mod_src = indoc! patterns with different string literal types
    { regex: /let\s+mod_src\s*=\s*indoc!\s*\{\s*"([^"\\]*(\\.[^"\\]*)*)"\s*\}\s*;/g, isIndoc: true, stringType: 'regular' },
    { regex: /let\s+mod_src\s*=\s*indoc!\s*\{\s*r"([^"\\]*(\\.[^"\\]*)*)"\s*\}\s*;/g, isIndoc: true, stringType: 'raw' },
    { regex: /let\s+mod_src\s*=\s*indoc!\s*\{\s*r#"([^"]*(?:"(?!#)[^"]*)*)"#\s*\}\s*;/g, isIndoc: true, stringType: 'raw_hash' },
  ];

  for (const pattern of patterns) {
    let match;
    while ((match = pattern.regex.exec(content)) !== null) {
      let code = match[1];

      // Process escape sequences based on the string literal type
      if (pattern.stringType === 'regular') {
        // For regular strings, unescape JavaScript-style escape sequences
        code = unescapeString(code);
      }
      // raw and raw_hash strings don't process escape sequences, so leave them as-is

      // Apply indoc processing if this is an indoc! pattern
      if (pattern.isIndoc) {
        code = unindent(code);
      }

      // Skip empty or very short snippets
      if (code.trim().length > 0) {
        snippets.push({
          code: code.trim(),
          isIndoc: pattern.isIndoc,
          stringType: pattern.stringType,
          type: getPatternType(pattern.isIndoc, pattern.stringType), // Keep for compatibility
          line: getLineNumber(content, match.index)
        });
      }
    }
  }

  return snippets;
}

function getPatternType(isIndoc, stringType) {
  // Generate a descriptive type string for compatibility
  if (isIndoc) {
    return `indoc_${stringType}`;
  }
  return stringType;
}

function getLineNumber(content, index) {
  return content.substring(0, index).split('\n').length;
}

// Function to unindent strings like Rust's indoc! macro
function unindent(text) {
  const lines = text.split('\n');

  // Find the minimum indentation of non-empty lines
  let minIndent = Infinity;
  for (const line of lines) {
    if (line.trim().length > 0) {
      const indent = line.match(/^[ \t]*/)[0].length;
      minIndent = Math.min(minIndent, indent);
    }
  }

  // If no non-empty lines found or no common indentation, return as-is
  if (minIndent === Infinity || minIndent === 0) {
    return text;
  }

  // Remove the common indentation from all lines
  return lines.map(line => {
    if (line.trim().length === 0) {
      return line; // Keep empty lines as-is
    }
    return line.slice(minIndent);
  }).join('\n');
}

// Function to unescape string literals (for regular strings, not raw strings)
function unescapeString(str) {
  return str.replace(/\\(.)/g, (match, char) => {
    switch (char) {
      case 'n': return '\n';
      case 't': return '\t';
      case 'r': return '\r';
      case '\\': return '\\';
      case '"': return '"';
      case "'": return "'";
      case '0': return '\0';
      default: return char; // For any other escaped character, just return the character
    }
  });
}

// Function to recursively find all .rs files in tests/language directory
function findRustFiles(dir) {
  const files = [];
  const entries = readdirSync(dir);

  for (const entry of entries) {
    const fullPath = join(dir, entry);
    const stat = statSync(fullPath);

    if (stat.isDirectory()) {
      files.push(...findRustFiles(fullPath));
    } else if (entry.endsWith('.rs')) {
      files.push(fullPath);
    }
  }

  return files;
}

function analyzeParseResult(code, tree) {
  const results = {
    hasErrors: false,
    errorNodes: [],
    nodeTypes: new Set(),
    nodeCount: 0
  };

  const cursor = tree.cursor();
  do {
    results.nodeCount++;
    results.nodeTypes.add(cursor.type.name);

    if (cursor.type.isError) {
      results.hasErrors = true;
      results.errorNodes.push({
        type: cursor.type.name,
        from: cursor.from,
        to: cursor.to,
        text: code.slice(cursor.from, cursor.to)
      });
    }
  } while (cursor.next());

  return results;
}

function printCompactTree(node, code, maxDepth = 2, currentDepth = 0) {
  if (currentDepth > maxDepth) return '';

  const indent = '     ' + '  '.repeat(currentDepth);
  const text = code.slice(node.from, node.to);
  const preview = text.length > 30 ? text.slice(0, 30) + '...' : text;

  let result = `${indent}${node.type.name} [${node.from}-${node.to}] "${preview}"\n`;

  if (node.firstChild && currentDepth < maxDepth) {
    let child = node.firstChild;
    do {
      result += printCompactTree(child, code, maxDepth, currentDepth + 1);
    } while (child = child.nextSibling);
  }

  return result;
}

function testCodeSnippet(snippet, index, total) {
  try {
    const tree = parser.parse(snippet.code);
    const analysis = analyzeParseResult(snippet.code, tree);

    if (analysis.hasErrors) {
      // Always show full error details for failed tests
      if (verboseMode) {
        console.log('');
      }
      console.log(`❌ Test ${index + 1}/${total}: From ${snippet.file}:${snippet.line} (${snippet.type})`);

      // Show the code snippet
      const lines = snippet.code.split('\n');
      if (lines.length > 1) {
        console.log('   Code:');
        lines.forEach((line, i) => {
          console.log(`   ${String(i + 1).padStart(3)}: ${line}`);
        });
      } else {
        console.log(`   Code: "${snippet.code}"`);
      }

      console.log('   Parse errors:');
      for (const error of analysis.errorNodes) {
        const errorText = error.text.replace(/\n/g, '\\n');
        console.log(`     ${error.type} at ${error.from}-${error.to}: "${errorText}"`);
      }
      return false;
    } else {
      // Success case
      if (verboseMode) {
        // Detailed mode: show full information
        console.log(`\n✅ Test ${index + 1}/${total}: From ${snippet.file}:${snippet.line} (${snippet.type})`);

        const lines = snippet.code.split('\n');
        if (lines.length > 1) {
          console.log('   Code:');
          lines.forEach((line, i) => {
            console.log(`    ${String(i + 1).padStart(3)}: ${line}`);
          });
        } else {
          console.log(`   Code: "${snippet.code}"`);
        }

        console.log(`   Parsed successfully: ${analysis.nodeCount} nodes, ${analysis.nodeTypes.size} unique types`);

        // Show tree for shorter examples in detailed mode
        if (snippet.code.length < 200) {
          console.log('   Parse Tree:');
          console.log(printCompactTree(tree.topNode, snippet.code));
        }
      } else if (!errorsOnly) {
        // Normal mode: simple one-line success message
        console.log(`✅ Test ${index + 1}/${total}: From ${snippet.file}:${snippet.line} (${snippet.type})`);
      }
      return true;
    }
  } catch (error) {
    console.log(`\n💥 Test ${index + 1}/${total}: From ${snippet.file}:${snippet.line} (${snippet.type})`);
    console.log(`💥 Exception: ${error.message}`);
    return false;
  }
}

// Main execution
console.log('🔍 Extracting Ferlium code snippets from test files...');

const testsDir = '../../tests/language';  // Adjusted path from playground/test/ to tests/language
const rustFiles = findRustFiles(testsDir);

console.log(`Found ${rustFiles.length} Rust test files`);

let allSnippets = [];

for (const file of rustFiles) {
  try {
    const content = readFileSync(file, 'utf8');
    const snippets = extractCodeSnippets(content);

    // Add file information to each snippet
    for (const snippet of snippets) {
      snippet.file = file.replace('../../tests/language/', '');
      allSnippets.push(snippet);
    }

    if (verboseMode) {
      console.log(`📄 ${file.replace('../../tests/language/', '')}: ${snippets.length} snippets`);
    }
  } catch (error) {
    console.error(`❌ Error reading ${file}: ${error.message}`);
  }
}

console.log(`📊 Total extracted snippets: ${allSnippets.length}`);

if (allSnippets.length === 0) {
  console.log('⚠️  No code snippets found. Make sure the tests/language directory exists and contains .rs files with run() calls.');
  process.exit(1);
}

// Sort snippets by file and line number for consistent testing order
allSnippets.sort((a, b) => {
  if (a.file !== b.file) return a.file.localeCompare(b.file);
  return a.line - b.line;
});

if (verboseMode) {
  console.log('\n🚀 Starting grammar testing with extracted snippets...');
}

let passed = 0;
let failed = 0;

for (let i = 0; i < allSnippets.length; i++) {
  const success = testCodeSnippet(allSnippets[i], i, allSnippets.length);
  if (success) {
    passed++;
  } else {
    failed++;
  }
}

// Ensure we end with a newline
console.log('');

console.log(`\n${'='.repeat(80)}`);
console.log(`🎯 FINAL RESULTS`);
console.log(`${'='.repeat(80)}`);
console.log(`✅ Passed: ${passed}`);
console.log(`❌ Failed: ${failed}`);
console.log(`📊 Success Rate: ${((passed / (passed + failed)) * 100).toFixed(1)}%`);

if (failed === 0) {
  console.log('\n🎉 All extracted snippets parsed successfully!');
  process.exit(0);
} else {
  console.log(`\n⚠️  ${failed} snippets failed to parse. Check the output above for details.`);
  process.exit(1);
}
