import React from 'react';
import ReactDOM from 'react-dom';
import BoxInfo from './BoxInfo';

it('renders without crashing', () => {
  const div = document.createElement('div');
  ReactDOM.render(<BoxInfo />, div);
  ReactDOM.unmountComponentAtNode(div);
});
