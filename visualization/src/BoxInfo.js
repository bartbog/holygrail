import './App.css';
import React from 'react';
import './BoxInfo.css';
// import * as R from 'ramda'
import ReactDOM from 'react-dom';

const problemName = 'niels-split';

const cluesTags = require(`../../bos/output/${problemName}.tags.json`);

var selectedBox = 0;

const cluesIntroText = "ZebraTutor starts from a plain English language representation of the clues (and a list of all the entities present in the puzzle) :"
const tagsIntroText = "Each word from each natural language clue is tagged using the NTLK perceptron tagger. The output of the POS-tagging process are Part-Of-Speech tagged words:"
const lexiconIntroText = "The input of our system consists of these clues, combined with the following lexicon (the automated lexicon building does not yet work fully automatically):"

var activeClue = 0;

var displayTypes = {
  clues: 1,
  postags: 2,
  chunking_lexicon: 3,
  fol: 4,
  idp: 5,
  expl: 6
};

function setToClue(clueNr) {

  if (clueNr >= cluesTags["tags"].length) {
    activeClue = cluesTags["tags"].length - 1;
  } else if (clueNr <= 0) {
    activeClue = 0;
  } else {
    activeClue = clueNr;
  }


  for (let index = 0; index < cluesTags["tags"].length; index++) {
    const tagName = `tag${index}`
    var tagChild = document.getElementById(tagName);
    if (activeClue === index) {
      tagChild.style.display = 'block';
    } else {
      tagChild.style.display = 'none';
    }
  }
}


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

  var listItems = [];

  for (let index = 0; index < tags.length; index++) {
    const element = tags[index];
    const keyElem = `tag${index}`
    if (index === activeClue) {
      listItems.push(
      <div id={keyElem}>
        <table>
          <tr>{element.map((elem) => <td className="td-clues-tags thick-text">{elem[0]}</td>)}</tr>
          <tr>{element.map((elem) => <td className="td-clues-tags">|</td>)}</tr>
          <tr >{element.map((elem) => <td className="td-clues-tags thick-text">{elem[1]}</td>)}</tr>
        </table>
      </div>)
    } else {
      listItems.push(
      <div className="HiddenBox" id={keyElem}>
        <table>
          <tr>{element.map((elem) => <td className="td-clues-tags thick-text">{elem[0]}</td>)}</tr>
          <tr>{element.map((elem) => <td className="td-clues-tags">|</td>)}</tr>
          <tr >{element.map((elem) => <td className="td-clues-tags thick-text">{elem[1]}</td>)}</tr>
        </table>
      </div>)
    }
  }

  var clueBox = <div>    {introText}
    <div className="container">
      <div className="row">
        <div className="col" ></div>
        <div id="prev-clue" ><button className="col" onClick={() => setToClue(activeClue - 1)}>Previous Clue</button></div>
        <div id="next-clue"><button className="col" onClick={() => setToClue(activeClue + 1)}>Next Clue</button></div>
        <div className="col" ></div>
      </div>
      <div className="row padding-before-clue">
        
      <div className="col" ></div>
        <div >
          {listItems}
        </div>
        <div className="col" ></div>
      </div>
    </div>
    <br></br>

  </div>
  // const listItems = tags.map((clue) =>
  //   <div>
  //     <table>
  //       <tr>{clue.map((elem) => <td className="td-clues-tags thick-text">{elem[0]}</td>)}</tr>
  //       <tr>{clue.map((elem) => <td className="td-clues-tags">|</td>)}</tr>
  //       <tr >{clue.map((elem) => <td className="td-clues-tags thick-text">{elem[1]}</td>)}</tr>
  //     </table>
  //     <br></br>
  //     <br></br>
  //   </div>
  // );





  return clueBox
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
    <div className="row">
      <div id="BoxInfoText" className="BoxInfoText2 col-12">
      </div>
    </div>
  </div>)
}

function InfoButtons() {
  return (<div className="BoxInfo">
    <div className="row">
      <div id="clue-button" className="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.clues)}>1. Input</button></div>
      <div id="pos-button" className="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.postags)}>2. Pos Tagging</button></div>
      <div id="chun-button" className="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.chunking_lexicon)}>3. Chunking & Lexicon Building</button></div>
      <div id="fol-button" className="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.fol)}>4. First-Order Logic</button></div>
      <div id="idp-button" className="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.idp)}>5. IDP</button></div>
      <div id="expl-button" className="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.expl)}>6. Explanation Generation</button></div>
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
