// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

import { createApp } from 'vue';
import './style.css';
import App from './App.vue';
import init, { init_rust_api } from 'script-api';
import { reportEngineTrap } from './crash-recovery';


console.info(`Ferlium script playground rev ${__GIT_REVISION__}`);
const rev = `Ferlium rev. ${__GIT_REVISION__.slice(0, 8)}`;
init().then(() => {
	init_rust_api();
	const app = createApp(App);
	app.config.errorHandler = error => {
		reportEngineTrap(error);
		console.error(error);
	};
	app.mount('#app');
	for (const element of document.getElementsByClassName('revision')) {
		element.innerHTML = rev;
	}
})
