import React from 'react';
import './App.css';
import 'bootstrap/dist/css/bootstrap.css';
import 'bootstrap/dist/js/bootstrap.js';

// import ReactDOM from 'react-dom';

const tagsIntroText = <div><p>ZebraTutor is an end-to-end solution for solving logic grid puzzles and for explaining, in a human-understandable way, how this solution can be obtained from the clues. Here is an example puzzle. The computer has already solved the problem ! But can you solve it ? </p><p className="centered-text"> Click <b>prev</b> and <b>next</b> to navigate in the human-like solving process.</p></div>

const blockQuoteIntroText = <div className="puzzle-text"><i>{tagsIntroText} </i></div>

function PuzzleInfo() {
  return (
    <div >
      <h2 className="centered-text">Zebra Tutor: a Holy Grail</h2>
      <div>
        {blockQuoteIntroText}
      </div>
    </div>
  );
}

export default PuzzleInfo;