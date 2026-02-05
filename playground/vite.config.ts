// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
import { defineConfig } from 'vite';
import { execSync } from 'child_process';
import vue from '@vitejs/plugin-vue';
import eslintPlugin from "@nabla/vite-plugin-eslint";
import wasmPack from 'vite-plugin-wasm-pack';
import mkcert from'vite-plugin-mkcert';
import lezer from 'unplugin-lezer/vite';

const gitCommitHash = execSync('git rev-parse HEAD').toString().trimEnd();

// https://vitejs.dev/config/
export default defineConfig({
  base: "/ferlium/playground/",
  plugins: [vue(),
    eslintPlugin(),
    wasmPack(['./script-api']),
    mkcert({mkcertPath: '/usr/bin/mkcert'}),
    lezer(),
  ],
  define: {
    // Define a global constant for the git revision
    '__GIT_REVISION__': JSON.stringify(gitCommitHash)
  },
});
