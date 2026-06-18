#include<bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n,s,r;
        cin>>n>>s>>r;
        int arr[n];
        arr[0]= s-r;
        for(int i=1;i<n;i++){
            arr[i]=1;
            r--;
        }
        for(int i=1;i<n;i++){
            if(r==0)    break;
            arr[i]+=1;
            r--;
            if(r>0&&i==n-1) i=0;
        }
        for(int i=0;i<n;i++){
            cout<<arr[i]<<" ";
        }
        cout<<endl;
    }
}