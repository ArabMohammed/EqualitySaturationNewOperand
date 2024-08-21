import random
class Matrix : 
   
    def __init__(self, nb_rows,nb_cols):
        self.nb_rows = nb_rows
        self.nb_cols = nb_cols 
    
def generate_matrix(mat : Matrix): 
    result = []
    for i in range(mat.nb_rows): 
        temp = []
        for j in range(mat.nb_cols): 
            temp.append(random.randrange(-5,5))
        result.append(temp)
    return result 
def multiply_matrixes(A : Matrix,B : Matrix): 
    C = Matrix(nb_rows=A.nb_rows,nb_cols=B.nb_cols)
    result = []
    result = [[sum(A.value[i][k] * B.value[k][j] for k in range(A.nb_cols)) for j in range(B.nb_cols)] for i in range(A.nb_rows)]
    C.value = result
    return C
function_slot_count= 128
is_cipher = 1 
is_signed = 1
matrix_A = Matrix(nb_rows=function_slot_count,nb_cols=function_slot_count)
matrix_B = Matrix(nb_rows=function_slot_count,nb_cols=function_slot_count)
matrix_A.value = generate_matrix(matrix_A)
matrix_B.value = generate_matrix(matrix_B)
matrix_C = multiply_matrixes(matrix_A,matrix_B)
## writing matrix to file  
with open("matrix_mul_io_example.txt","w") as file : 
    nb_inputs= matrix_A.nb_rows + matrix_B.nb_cols 
    nb_outputs = matrix_A.nb_rows 
    header = str(function_slot_count)+" "+str(nb_inputs)+" "+str(nb_outputs)+"\n"
    file.write(header) 
    rows=[]
    for i in range(matrix_A.nb_rows): 
        row = "A[{}][]".format(i)+" "+str(is_cipher)+" "+str(is_signed)+" "+" ".join(str(num) for num in matrix_A.value[i])+"\n"
        rows.append(row)
    file.writelines(rows)
    cols = []
    for j in range(matrix_B.nb_cols):
        col = "B[][{}]".format(j)+" "+str(is_cipher)+" "+str(is_signed)+" "+" ".join(str(matrix_B.value[i][j]) for i  in range(matrix_B.nb_rows))+"\n"
        cols.append(col)
    file.writelines(cols)
    rows=[]
    for i in range(matrix_C.nb_rows): 
        row = "C[{}][]".format(i)+" "+str(is_cipher)+" "+" ".join(str(num) for num in matrix_C.value[i])+"\n"
        rows.append(row)
    file.writelines(rows)