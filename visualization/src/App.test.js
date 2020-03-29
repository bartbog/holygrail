import React from 'react';
import ReactDOM from 'react-dom';
import App from './App';

const problemName = 'nielspasta-split-nested'; //pasta


it('renders without crashing', () => {

  const div = document.createElement('div');
  ReactDOM.render(<App problemName={problemName} />, div);
  ReactDOM.unmountComponentAtNode(div);
});
