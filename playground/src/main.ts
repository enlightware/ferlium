// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
import { createApp } from 'vue';
import './style.css';
import App from './App.vue';
import init, { init_rust_api } from 'script-api';


console.info(`Ferlium script playground rev ${__GIT_REVISION__}`);
const rev = `Ferlium rev. ${__GIT_REVISION__.slice(0, 8)}`;
init().then(() => {
	init_rust_api();
	createApp(App).mount('#app');
	for (const element of document.getElementsByClassName('revision')) {
		element.innerHTML = rev;
	}
})
