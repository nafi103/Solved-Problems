#include<bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n;
        cin>>n;
        int arr[n][n-1];
        int f[n+1] ={0};
        for(int i=0;i<n;i++){
            for(int j=0;j<n-1;j++){
                cin>>arr[i][j];
            }
            f[arr[i][0]]++;
        }
        int j = INT_MIN;
        for (int i = 1; i <= n; i++)
        {
            if(f[i]==n-1)   j = i;
        }
        cout<<j<<" ";
        for (int i = 0; i < n; i++)
        {
            if(arr[i][0]!=j){
                for(int k = 0; k < n-1; k++){
                    cout<<arr[i][k]<<" ";
                }
                break;
            }
        }
        cout<<endl;
    }
}