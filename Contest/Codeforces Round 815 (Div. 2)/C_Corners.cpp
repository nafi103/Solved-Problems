#include<bits/stdc++.h>
using namespace std;
 void solution(){
    int n,m, sum= 0, tsum, min1L = 3;
    string x;
    cin>> n >>m;
    int arr[n][m];
    for(int i = 0; i<n; i++){
        cin>>x;
        for (int j = 0; j < m; j++)
        {
            arr[i][m-1-j]= (int)(x[x.size()-1])-48;
            x.pop_back();
            sum += arr[i][m-1-j];
        }
    }
    for (int i = 0; i < n-1; i++)
    {
        for (int j = 0; j < m-1; j++){
            tsum = arr[i][j]+arr[i+1][j]+arr[i][j+1]+arr[i+1][j+1];
            if(tsum-1<min1L){
                min1L = tsum-1;
                if(min1L<=0) break;
            }
        }
    }
    if(min1L<0) min1L = 0;
    cout<<sum- min1L+((min1L==0)?0:1)<<endl;
}
 int main(){
    int t;
    cin>> t;
    while(t--)  solution();
}