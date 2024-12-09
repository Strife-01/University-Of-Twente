import numpy as np
reference_set = np.array([[1.4,0.2],[1.5,0.2],[1.7,0.4],[1.5,0.2],[1.5,0.1],[1.6,0.2],[1.1,0.1],[1.5,0.4],[1.4,0.3],[1.5,0.3],[1.5,0.4],[1.7,0.5],[1.6,0.2],[1.5,0.2],[1.6,0.2],[1.5,0.4],[1.4,0.2],[1.2,0.2],[1.4,0.1],[1.5,0.2],[1.3,0.3],[1.6,0.6],[1.4,0.3],[1.4,0.2],[1.4,0.2],[4.5,1.5],[4.,1.3],[4.5,1.3],[3.3,1.],[3.9,1.4],[4.2,1.5],[4.7,1.4],[4.4,1.4],[4.1,1.],[3.9,1.1],[4.,1.3],[4.7,1.2],[4.4,1.4],[5.,1.7],[3.5,1.],[3.7,1.],[5.1,1.6],[4.5,1.6],[4.4,1.3],[4.,1.3],[4.6,1.4],[3.3,1.],[4.2,1.2],[4.3,1.3],[4.1,1.3],[5.1,1.9],[5.6,1.8],[6.6,2.1],[6.3,1.8],[6.1,2.5],[5.3,1.9],[5.,2.],[5.3,2.3],[6.7,2.2],[5.,1.5],[4.9,2.],[4.9,1.8],[6.,1.8],[4.9,1.8],[5.8,1.6],[6.4,2.],[5.1,1.5],[6.1,2.3],[5.5,1.8],[5.4,2.1],[5.1,2.3],[5.9,2.3],[5.2,2.3],[5.2,2.],[5.1,1.8]])
reference_labels = np.array([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2])
test_set = np.array([[1.13,0.17],[1.37,0.4],[1.27,0.47],[1.05,0.28],[1.46,0.24],[1.14,0.08],[1.47,-0.14],[1.36,0.38],[1.16,0.88],[1.81,0.13],[1.26,-0.01],[1.16,0.42],[2.12,0.14],[1.89,0.37],[1.53,-0.11],[1.36,-0.19],[1.14,0.55],[1.34,0.12],[1.42,-0.16],[0.87,0.59],[1.11,0.07],[1.02,-0.2],[1.8,0.54],[1.67,0.53],[1.22,-0.13],[4.59,1.54],[4.56,1.72],[4.87,1.48],[4.33,1.76],[4.26,0.94],[3.42,1.21],[3.87,0.98],[3.45,1.4],[4.69,1.44],[4.7,1.21],[4.56,2.25],[5.,1.27],[4.36,1.16],[5.36,1.06],[4.61,1.19],[3.78,0.99],[3.77,1.34],[4.44,1.53],[4.76,1.47],[3.94,1.55],[4.65,1.18],[3.87,1.39],[4.06,1.13],[4.72,1.3],[2.61,1.35],[6.15,2.16],[5.9,2.04],[5.99,2.42],[4.7,1.51],[5.58,2.15],[4.46,2.11],[5.98,1.67],[4.76,2.12],[5.56,1.83],[7.03,2.43],[6.,2.69],[6.63,1.88],[6.04,2.11],[4.99,1.83],[5.31,1.98],[6.51,1.9],[5.22,2.12],[5.82,1.84],[5.75,2.58],[4.55,1.82],[5.9,2.45],[5.25,2.35],[5.76,2.21],[4.51,1.59],[5.58,2.41]])
# implement here the kNN classifier

def knn(reference_set, ref_labels, test_sample, k):
    C = 0  # class
    # your code here
    x1, y1 = test_sample
    class_set = set(ref_labels)
    class_decider_dict = {cl: 0 for cl in class_set}
    distance_list = sorted([[np.sqrt((reference_set[i][0] - x1) ** 2 + (reference_set[i][1] - y1) ** 2), i] for i in range(len(reference_set))])[:k]
    for element in distance_list:
        class_decider_dict[reference_labels[element[1]]] += 1
    C = max(class_decider_dict, key=class_decider_dict.get)
    # end: your code here
    return C

k = 5
#k = 3
#k = 5

predicted_class_list = [knn(reference_set, reference_labels, test_data, k) for test_data in test_set]
print(predicted_class_list)

confusion_matrix = np.zeros((3, 3), dtype=int)

# Populate the confusion matrix
for true, pred in zip(reference_labels , predicted_class_list):
    confusion_matrix[true, pred] += 1

print(confusion_matrix)
# Populate the confusion matrix
for ground_truth, predicted in zip(reference_labels , predicted_class_list): # zip creates an object which corelates 1 to 1 values in the 2 provided lists based on index
    confusion_matrix[ground_truth, predicted] += 1 # it updates the values in the array

correct_predictions = np.trace(confusion_matrix) # sum all the values on the i=j diagonal
total_prediction = np.sum(confusion_matrix) # sum all the values in the matrix
accuracy = correct_predictions / total_prediction
print(accuracy)
