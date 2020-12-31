import React from 'react';
import ReactDOM from 'react-dom';
import './index.css';
import App from './App';
import BoxInfo from './BoxInfo';
import PuzzleInfo from './PuzzleInfo';
import * as serviceWorker from './serviceWorker';
import 'bootstrap/dist/css/bootstrap.css';
import 'bootstrap/dist/js/bootstrap.js';


//const problemName = 'p5-split-nested'; //pasta
//  const problemName = 'nielspasta-split-nested'; //pasta
const problemName = 'expl_seq'; //pasta

console.log(problemName)

ReactDOM.render( <PuzzleInfo /> , document.getElementById('problemIntro'));
ReactDOM.render( <App problemName={problemName} /> , document.getElementById('root'));
ReactDOM.render( <BoxInfo problemName={problemName}  />, document.getElementById('box-info'));

// If you want your app to work offline and load faster, you can change
// unregister() to register() below. Note this comes with some pitfalls.
// Learn more about service workers: https://bit.ly/CRA-PWA
serviceWorker.unregister();
