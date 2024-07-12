import { createApp } from 'vue';
import './style.css';
import App from './App.vue';
import init, { init_rust_api } from 'script-api';


console.info(`Enlightware script playground rev ${__GIT_REVISION__}`);
init().then(() => {
	init_rust_api();
	createApp(App).mount('#app');
})
