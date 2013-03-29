class Square
{  
    static int printN(int N, int x)
	{
        for(int i = 0; i < N; i++) {
            BuiltIn.printInt(x);
        }
        return 0;
    }
  
    static int main() 
	{
        int size = BuiltIn.readInt();
        if(size < 2)
      return 0;
    printN(size, 0);
    BuiltIn.newLine();
    for(int i = 0; i < size - 2; i++) {
      BuiltIn.printInt(0);
      for(int j = 0; j < size - 2; j++) {
        BuiltIn.printInt(0);
      }
      BuiltIn.printInt(0);
      BuiltIn.newLine();
    }
    printN(size, 0);
    BuiltIn.newLine();
    return 0;
  }
}
