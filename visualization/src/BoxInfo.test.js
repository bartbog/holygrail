import React from 'react';
import ReactDOM from 'react-dom';
import BoxInfo from './BoxInfo';

const problemName = 'nielspasta-split-nested'; //pasta


it('renders without crashing', () => {
  const div = document.createElement('div');
  ReactDOM.render(<BoxInfo problemName={problemName}  />, div);
  ReactDOM.unmountComponentAtNode(div);
});
