import './App.css';
import React from 'react';
import './BoxInfo.css';
// import * as R from 'ramda'
import ReactDOM from 'react-dom';

const problemName = 'niels-split';

const cluesTags = require(`../../bos/output/${problemName}.tags.json`);

var selectedBox = 0;

const cluesIntroText = "ZebraTutor starts from a plain English language representation of the clues (and a list of all the entities present in the puzzle):"
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
        <Clues clues={cluesTags["clues"]} entities={cluesTags["types"]} />,
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

function cleanEntities(entities){
  const types = Object.keys(entities).map((elem)=> elem.toLowerCase());
  const cleanedEntities = Object.keys(entities)
                                .map((elem)=> entities[elem]
                                .map((entity) => entity.replace("a_", "").split('_')
                                .map((splitelem) => types.push(splitelem))))
                                
                                
                                
                                
                                // types.push(entity.toLowerCase().replace("a_", "").replace('_', ' '))))
  return types;
}

function highlightEntities(clue, entities){
  const cleanedEntities = cleanEntities(entities)

  const cleanedClues = clue.split(' ').map(function(elem) {
    if((cleanedEntities.indexOf(elem) !== -1)){
      return <b>{elem} </b>
    }else{
      return elem + " "
    }
    });
  const joinedClues= cleanedClues

  // return <td className="thick-text">{clue.charAt(0).toUpperCase() + clue.slice(1)}.</td>
  return <td><div>{joinedClues}</div></td>
}

function Clues({ clues, entities }) {

  const listClues = clues.map((elem) =>
    <div>
      <tr>
        {highlightEntities(elem, entities)}
      </tr>
    </div>
  );
  // const listEntities = JSON.stringify(entities);
  const entitiesTable = <table>
    <tr>
      <th></th>
      {Object.keys(entities).map((elem) => <th></th>)}
    </tr>
    {Object.keys(entities).map((elem) =>
      <tr>
        <td className="thick-text">{elem.charAt(0).toUpperCase() + elem.slice(1)}</td>
        {entities[elem].map((entity) => <td className="td-entities">{entity}</td>)}
      </tr>)}
  </table>;

  const introText = <div className="grey-text"> {cluesIntroText}</div>
  const cluesTable = <table>{listClues}</table>
  // const entitiesTable = <table>{listEntities}</table>
  return (
    <div >
      {introText}
      <h2 className="BoxInfoText3-Header">Entities</h2>
      <div className="BoxInfoText3">
        {entitiesTable}
      </div>
      <h2 className="BoxInfoText3-Header">Clues</h2>
      <div className="BoxInfoText3">
        {cluesTable}
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
  return (

    <div className="row">
      <div id="BoxInfoTextParent" className="col-12">
        <div id="BoxInfoText" className="BoxInfoText2">
        </div>
      </div>

    </div>
  )
}

function InfoButtons() {
  return (
    <div className="row">
      <div id="clue-button" className="col-sm"><button className="button-step3" onClick={() => setBoxInfoDisplayTo(displayTypes.clues)}>Input</button></div>
      <div className="div-centered-hv col-sm">----></div>
      <div id="pos-button" className="col-sm"><button className="button-step3" onClick={() => setBoxInfoDisplayTo(displayTypes.postags)}>Pos Tagging</button></div>
      <div className="div-centered-hv col-sm">----></div>
      <div id="chun-button" className="col-sm"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.chunking_lexicon)}>Chunking & Lexicon Building</button></div>
      <div className=" div-centered-hv col-sm">----></div>
      <div id="fol-button" className="col-sm"><button className="button-step2" onClick={() => setBoxInfoDisplayTo(displayTypes.fol)}>First-Order Logic</button></div>
      <div className=" div-centered-hv col-sm">----></div>
      <div id="idp-button" className="col-sm"><button className="button-step3" onClick={() => setBoxInfoDisplayTo(displayTypes.idp)}>IDP</button></div>
      <div className=" div-centered-hv col-sm">----></div>
      {/* <div id="expl-button" className="col-2"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.expl)}>6. Explanation Generation</button></div> */}
      {/* <div id="expl-button" className="col-sm"><button className="button-step" onClick={() => setBoxInfoDisplayTo(displayTypes.expl)}>6. Explanation Generation</button></div> */}
      <div className="div-centered-hv col-sm">Explanation Generation</div>
    </div>)
}

function BoxInfo() {
  return (
    <div>
      {/* <h2>The process</h2> */}
      <h2><span  class="line-center">The process</span></h2>

      <InfoButtons />
      <InfoText />
    </div>
  );
}

export default BoxInfo;
