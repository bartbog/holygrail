#!/usr/bin/env python3
# Download the puzzle problems from http://logicgridpuzzles.com/puzzles/
# Before running the program download following packages: 
# pip3 install urllib bs4 lxml

import requests
from urllib import request
from bs4 import BeautifulSoup
import lxml.html as lh
import re
from logicpuzzle import LogicPuzzle

weburl = "http://logicgridpuzzles.com/puzzles/show_logic.php"

def urlactive(url = weburl):
    ''' Check if the weburl is active 
    @param url (string): valid website url
    '''
    response = requests.get(url)
    return response.status_code == 200

def clean(text):
    '''Remove trailing spaces, capitalize and clean text from any garbage symbols or letters.

    @param text (string): text to clean 
    '''
    if not text:
        return ''
    return text.replace(u'\xa0', u' ').replace('\n','').replace('&nbsp', '').replace('\t','').lower().strip().capitalize()

def getPuzzleUrl(puzzleID):
    '''Construct puzzle url associated to puzzleID

    @param puzzleID (int): ID of the puzzle on the http://logicgridpuzzles.com/puzzles/ website
    '''
    puzzleUrl = weburl + '?ID=' + str(puzzleID)
    return puzzleUrl

def extractPuzzleClues(soup):
    '''Extract the puzzle clues from html into a list of clues

    @param soup (beautifulsoup): html extracted with beautifulsoup
    @return clues (list<string>) : list of puzzle clues
    '''
    listItems = soup.find('ol').findAll('li')
    clues = [clean(i.text) for i in listItems]
    return clues

def extractPuzzleDomain(soup):
    '''Extract the puzzle types/domain from the html 

    @param soup (beautifulsoup): html extracted with beautifulsoup
    @return puzzleDomain (dict<string:string>) : dictionnary of variables with their corresponding domain
    '''
    puzzleDomain = {}
    table = soup.find('form', {'id': 'myForm1'}).find('table')
    domainVariables = [clean(th.text) for th in table.findAll('tr')[0].findAll('th')]
    for variable in domainVariables:
        puzzleDomain[variable] = []

    for td in table.findAll('td', {'align':None}):
        if not td.find('option'):
            puzzleDomain[domainVariables[0]].append(td.text)

    idx = 1
    for td in table.findAll('tr')[1].findAll('td'):
        if td.find('select'):
            curVariable = domainVariables[idx]
            options = td.find('select').findAll('option', {'selected':None})
            for option in options : 
                puzzleDomain[curVariable].append(option.text)
            idx+=1

    return puzzleDomain 

def extractPuzzleInfo(soup):
    '''Extract the puzzle meta data (title, user, difficulty and problem stateent) from the html 

    @param soup (beautifulsoup): html extracted with beautifulsoup
    @return problemdict (dict<string:string>) : dictionnary of meta-data of the puzzle
    '''
    problemInfotd = soup.find('td', {'align': 'left'})
    title = clean(problemInfotd.find('h3').text)
    h4info = problemInfotd.findAll('h4')
    user = clean(h4info[0].text).lower().replace('submitted by','').replace(':', '')
    difficulty = clean(h4info[1].text).lower().replace('difficulty','').replace(':', '').strip()    
    problemtext = soup.find('p').text
    cleanproblemtext = problemtext.replace('\r','')
    problemstatement  = re.sub('[^(\w|:|.|\'|,|?|\&|\n)]',' ', cleanproblemtext)
    splittedproblem = re.split('\n|\w{3,}\.', problemstatement)
    problemphrases = [statement.strip() for statement in splittedproblem if statement.strip() != '' ]

    problemdict = {
        'title':title,
        'user':user,
        'difficulty':difficulty,
        'problem':problemphrases
    }

    return problemdict

def buildLogicPuzzle(puzzleID):
    '''Extract the puzzle number ``puzzmeID`` and build a LogicPuzzle object

    @param puzzleID: id of the puzzle
    @return puzzle (LogicPuzzle): LogicPuzzle object
    '''
    puzzleUrl = getPuzzleUrl(puzzleID)
    response = requests.get(puzzleUrl)
    soup = BeautifulSoup(response.text, 'lxml')

    # check if empty page
    if not soup.find('div'):
        return None
    
    puzzle = LogicPuzzle()

    puzzle.ID = puzzleID
    puzzle.url = puzzleUrl
    puzzle.clues = extractPuzzleClues(soup)
    puzzle.domain = extractPuzzleDomain(soup)
    # problem meta data
    problemdict = extractPuzzleInfo(soup)
    puzzle.title = problemdict['title']
    puzzle.user = problemdict['user']
    puzzle.diffulty = problemdict['difficulty']
    puzzle.problem = problemdict['problem']

    return puzzle

def downloadById(ID, dir= '', filename = ''):
    '''Downloads the puzzle number ``ID`` to the drive at directory ``dir\\filename``

    @param ID: id of the puzzle
    @param dir : download directory 
    @param filename : name of the downloaded file 
    '''
    puzzle = buildLogicPuzzle(ID)

    if puzzle:
        puzzle.downloadPuzzle(folderpath = dir, filename = filename)

def downloadRange(dir='', filename= '', start=1, end=211):
    '''Downloads a range start->end of puzzles to the drive at directory ``dir\\filename``

    @param start : Start problem id
    @param end : End problem id
    @param dir : Download directory 
    @param filename : Name of the downloaded file 
    '''
    if start < 1 or end < start or end < 1:
        raise Exception("Please specify valid range. start > 0  and start > end ")

    if start == end:
        downloadById(ID = start, dir = dir, filename = filename)

    for i in range(start, end+1):
        downloadById(ID = i, dir = dir, filename = filename)

def downloadAll(dir = '', filename =''):
    '''Downloads all available puzzles to the drive at directory ``dir\\filename``

    @param dir : Download directory 
    @param filename : Name of the downloaded file 
    '''
    # check if website is up
    if urlactive():
        # download everything
        downloadRange(dir = dir , filename = filename)

def main():
    downloadAll()

if __name__ == '__main__':
    main()
    