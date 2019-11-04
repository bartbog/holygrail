import React from 'react';
import './App.css';
import './BoxInfo.css';
// import * as R from 'ramda'
import ReactDOM from 'react-dom';

const problemName = 'p5';

const cluesTags = require(`../../bos/output/${problemName}.tags.json`);

var selectedBox = 0;

const cluesIntroText = "The clues are considered input together with puzzle problem statement:"
const tagsIntroText = "Each word from each setence is tagged using the NTLK perceptron tagger:"
const lexiconIntroText = "The input of our system consists of these clues, combined with the following lexicon (the automated lexicon building does not yet work fully automatically):"
const maxActiveClue = cluesTags["tags"].length
var activeCLue = 0;



var displayTypes = {
  clues: 1,
  postags: 2,
  chunking_lexicon: 3,
  fol: 4,
  idp: 5,
  expl: 6
};

function setBoxInfoDisplayTo(displayType) {

  if (selectedBox === displayType) {
    document.getElementById('BoxInfoText').style.display = "none";
    selectedBox = 0
  } else {
    document.getElementById('BoxInfoText').style.display = "block";
    selectedBox = displayType
  }


  switch (displayType) {
    case displayTypes.clues:
      ReactDOM.render(
        <Clues clues={cluesTags["clues"]} />,
        document.getElementById('BoxInfoText')
      );
      break;
    case displayTypes.postags:
      ReactDOM.render(
        <Tags tags={cluesTags["tags"]} />,
        document.getElementById('BoxInfoText')
      );
      break;
    case displayTypes.chunking_lexicon:
      ReactDOM.render(
        <Lexicon lexicon={cluesTags["lexicon"]} />,
        document.getElementById('BoxInfoText')
      );
      break;
    case displayTypes.fol:
      ReactDOM.render(
        <Clues clues={cluesTags["clues"]} />,
        document.getElementById('BoxInfoText')
      );
      break;
    case displayTypes.idp:
      ReactDOM.render(
        <Clues clues={cluesTags["clues"]} />,
        document.getElementById('BoxInfoText')
      );
      break;
    case displayTypes.expl:
      ReactDOM.render(
        <Clues clues={cluesTags["clues"]} />,
        document.getElementById('BoxInfoText')
      );
      break;
    default:

  }


}

function Clues({ clues }) {
  const listItems = clues.map((elem) =>
    <div>
      <tr>
        <td className="thick-text">{elem.charAt(0).toUpperCase() + elem.slice(1)}</td>
      </tr>
      <br></br>
    </div>
  );

  const introText = <div className="grey-text"> {cluesIntroText}
  </div>
  const lexiconTable = <table>{listItems}</table>
  return (
    <div>
    {introText}
    <div className="BoxInfoText3">
      {lexiconTable}
    </div>
  </div>)
}



function Tags({ tags }) {

  const introText = <div className="grey-text"> {tagsIntroText}</div>

  
  const listItems = tags.map((clue) =>
    <div>
      <table>
        <tr>{clue.map((elem) => <td className="td-clues-tags thick-text">{elem[0]}</td>)}</tr>
        <tr>{clue.map((elem) => <td className="td-clues-tags">|</td>)}</tr>
        <tr >{clue.map((elem) => <td className="td-clues-tags thick-text">{elem[1]}</td>)}</tr>
      </table>
      <br></br>
      <br></br>
    </div>
  );

  // function setActiveClue(clueNr){
  //   if(0 <= clueNr && clueNr < maxActiveClue ){
  //     activeCLue = clueNr;
  //   }
  // }

  // const listItems2 = 
  //   <div>
  //       <button onClick={() => setActiveClue(activeCLue - 1)}>Prev</button>
  //       <button onClick={() => setActiveClue(activeCLue + 1)}>Next</button>
  //     <table>
  //       <tr>{tags[activeCLue].map((elem) => <td className="td-clues-tags thick-text">{elem[0]}</td>)}</tr>
  //       <tr>{tags[activeCLue].map((elem) => <td className="td-clues-tags">|</td>)}</tr>
  //       <tr >{tags[activeCLue].map((elem) => <td className="td-clues-tags thick-text">{elem[1]}</td>)}</tr>
  //     </table>
  //     <br></br>
  //     <br></br>
  //   </div>

  return (<div>
    {introText}
    <div className="BoxInfoText3">
      {listItems}
    </div>
  </div>)
}

function Lexicon({ lexicon }) {
  const lexiconitems = Object.keys(lexicon).map((lex) =>
    <tr>
      <td className="thick-text">{lex}</td>
      <td className="td-clues-tags"></td>
      <td className="thick-text">{lexicon[lex]}</td>
    </tr>

  );
  const lexiconTable = <table>{lexiconitems}</table>
  const introText = <div className="grey-text"> {lexiconIntroText}  </div>

  return (
    <div>
      {introText}
      <div className="BoxInfoText3">
        {lexiconTable}
      </div>
    </div>)
}

function InfoText() {
  return (<div className="BoxInfoText">
    <div class="row">
      <div id="BoxInfoText" class="col-12" className="BoxInfoText2">
      </div>
    </div>
  </div>)
}

function InfoButtons() {
  return (<div className="BoxInfo">
    <div class="row">
      <div id="clue-button" class="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.clues)}>Clues</button></div>
      <div id="pos-button" class="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.postags)}>Pos Tagging</button></div>
      <div id="chun-button" class="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.chunking_lexicon)}>Chunking & Lexicon Building</button></div>
      <div id="fol-button" class="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.fol)}>First-Order Logic</button></div>
      <div id="idp-button" class="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.idp)}>IDP</button></div>
      <div id="expl-button" class="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.expl)}>Explanation Generation</button></div>
    </div>
  </div>)
}

function BoxInfo() {
  return (
    <div>
      <InfoButtons />
      <InfoText />
    </div>
  );
}

export default BoxInfo;
