import './App.css';
import React from 'react';
import './BoxInfo.css';
// import * as R from 'ramda'
import ReactDOM from 'react-dom';

const problemName = 'P5-split';

const cluesTags = require(`../../bos/output/${problemName}.tags.json`);

var selectedBox = 0;

const cluesIntroText = "ZebraTutor starts from a plain English language representation of the clues (and a list of all the entities present in the puzzle):"
const tagsIntroText = "Each word from each natural language clue is tagged using the NTLK perceptron tagger. The output of the POS-tagging process are Part-Of-Speech tagged words:"
const lexiconIntroText = "The input of our system consists of these clues, combined with the following lexicon (the automated lexicon building does not yet work fully automatically):"
const folIntroText = "The system outputs the first-order logic representation of the clues."
const idpIntroText = "Our tool then generates the following translation of each of the clues in the IDP language (where ! is a universal quantifier, ? is an existential quantifier, & is conjunction, | is disjunction and ~ is negation )"

var activeClue = 0;
var activeClueFol = 0;

var displayTypes = {
  clues: 1,
  postags: 2,
  chunking_lexicon: 3,
  fol: 4,
  idp: 5//,
  // expl: 6
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

    // const idpName = `idp${index}`
    // var idpChild = document.getElementById(idpName);
    if (activeClue === index) {
      tagChild.style.display = 'block';
      // idpChild.style.display = 'block';
    } else {
      tagChild.style.display = 'none';
      // idpChild.style.display = 'none';
    }
  }
}

function setToClueFol(clueNr) {

  if (clueNr >= Object.keys(cluesTags["fol-logic"]).length) {
    activeClueFol = Object.keys(cluesTags["fol-logic"]).length - 1;
  } else if (clueNr <= 0) {
    activeClueFol = 0;
  } else {
    activeClueFol = clueNr;
  }

  for (let index = 0; index < Object.keys(cluesTags["fol-logic"]).length; index++) {

    const folName = `fol${index}`
    var folChild = document.getElementById(folName);

    // const idpName = `idp${index}`
    // var idpChild = document.getElementById(idpName);
    if (activeClueFol === index) {

      folChild.style.display = 'block';
      // idpChild.style.display = 'block';
    } else {

      folChild.style.display = 'none';
      // idpChild.style.display = 'none';
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
        <FOL fol={cluesTags["fol-logic"]} />,
        document.getElementById('BoxInfoText')
      );
      break;
    case displayTypes.idp:
      ReactDOM.render(
        <IDP idp={cluesTags["idp"]} />,
        document.getElementById('BoxInfoText')
      );
      break;
    // case displayTypes.expl:
    //   ReactDOM.render(
    //     <Clues clues={cluesTags["clues"]} />,
    //     document.getElementById('BoxInfoText')
    //   );
    //   break;
    default:

  }
}

function IDP({idp}){

  
  const listIdpItems = Object.keys(idp).map((elem) => 
  <div className="padding-top">
    <tr >
      <td>// {elem}</td>
    </tr>
    <tr>
      <td>{idp[elem]}</td>
    </tr>
    </div>)
  const idpTable = <table>{listIdpItems}</table>
  const introText = <div className="grey-text"> {idpIntroText}</div>
  var clueBox = <div>{introText}
  <div className="BoxInfoText3 myFont">
    
        {idpTable}
     
  </div>
</div>

return clueBox
}


function FOL({fol}){
  const introText = <div className="grey-text"> {folIntroText}</div>
  const logicRepresentation = <h3>Logic representation</h3>
  const types = <h3>Types</h3>
  const CombTypes = <h3>CombTypes</h3>

  const fol_keys = Object.keys(fol);
  var listItems = []

  for (let index = 0; index < fol_keys.length; index++) {
    const key = fol_keys[index];
    const element = fol[key];
    const keyElem = `fol${index}`

    if (index === activeClue) {
      listItems.push(
        <div id={keyElem}>
          {logicRepresentation}
          <div >
          <table className="centered-div myFont">
          {element["logic_representation"].map(
            function(elem) {
              var listvals = []
              elem.split("").map(function(letter) {
                if(letter === " "){
                  listvals.push(" ")
                }else{
                  listvals.push(letter)
                }
              })
              return <tr className="removed-space"><td><pre>{listvals}</pre></td></tr>
            }) }
            </table>
            </div>
          {types}
          <div className="td-entities myFont">
          {element["types"].replace(/,/g, ', ') }
          </div>
          {CombTypes}
          <div className="td-entities myFont">
        {element["CombTypes"].replace(/,/g, ', ')}
        </div>
        </div>)
    } else {
      listItems.push(
        <div className="HiddenBox" id={keyElem}>
          {logicRepresentation}
          <div >
          <table className="centered-div myFont">
          {element["logic_representation"].map(
            function(elem) {
              var listvals = []
              elem.split("").map(function(letter) {
                if(letter === " "){
                  listvals.push(" ")
                }else{
                  listvals.push(letter)
                }
              })
              return <tr className="removed-space"><td><pre>{listvals}</pre></td></tr>
            }) }
            </table>
            </div>
          {types}
          <div className="td-entities myFont">
          {element["types"].replace(/,/g, ', ')}
          {/* {element["types"]} */}
          </div>
          {CombTypes}
          <div className="td-entities myFont">
        {element["CombTypes"].replace(/,/g, ', ')}
        {/* {element["CombTypes"]} */}
        </div>
        </div>)
    }
  }

  var clueBox = <div>    {introText}
    <div className="container">
      <div className="row">
        <div className="col" ></div>
        <div id="prev-clue" ><button className="col" onClick={() => setToClueFol(activeClueFol - 1)}>Previous Clue</button></div>
        <div id="next-clue"><button className="col" onClick={() => setToClueFol(activeClueFol + 1)}>Next Clue</button></div>
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


function cleanEntities(entities){
  const types = Object.keys(entities).map((elem)=> elem.toLowerCase());
  Object.keys(entities)
        .map((elem)=> entities[elem]
        .map((entity) => entity.replace("a_", "").split('_')
        .map((splitelem) => types.push(splitelem))))

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

  // return <td className="thick-text">{clue.charAt(0).toUpperCase() + clue.slice(1)}.</td>
  return <td><div>{cleanedClues}</div></td>
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
      <h2 className="BoxInfoText3-Header"><span className="line-center" >Entities</span></h2>
      <div className="BoxInfoText3 myFont">
        {entitiesTable}
      </div>
      <h2 className="BoxInfoText3-Header"><span className="line-center" >Clues</span></h2>
      <div className="BoxInfoText3 myFont">
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
        <div id={keyElem} className="myFont">
          <table>
            <tr>{element.map((elem) => <td className="td-clues-tags thick-text ">{elem[0]}</td>)}</tr>
            <tr>{element.map((elem) => <td className="td-clues-tags">|</td>)}</tr>
            <tr >{element.map((elem) => <td className="td-clues-tags thick-text">{elem[1]}</td>)}</tr>
          </table>
        </div>)
    } else {
      listItems.push(
        <div className="HiddenBox myFont" id={keyElem}>
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
      <div className="BoxInfoText3 myFont">
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
