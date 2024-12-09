list = [1,2,3,4,5,6]

list2 = list.map((item) => ++item)

console.log(list.filter((item) => {
  return item < 4;
}))

console.log(list.reduce((acc, curr) => {
  return acc += curr
}, 0))

console.log(list,'\n',list2)
