import { defineConfig } from 'vite';
import { execSync } from 'child_process';
import vue from '@vitejs/plugin-vue';
import eslintPlugin from "@nabla/vite-plugin-eslint";
import wasmPack from 'vite-plugin-wasm-pack';
import mkcert from'vite-plugin-mkcert';

const gitCommitHash = execSync('git rev-parse HEAD').toString().trimEnd();

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [vue(), eslintPlugin(), wasmPack(['./script-api']), mkcert({mkcertPath: '/usr/bin/mkcert'})],
  define: {
    // Define a global constant for the git revision
    '__GIT_REVISION__': JSON.stringify(gitCommitHash)
  },
});
