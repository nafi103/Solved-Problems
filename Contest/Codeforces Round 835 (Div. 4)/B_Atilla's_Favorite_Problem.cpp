#include <bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n;
        cin>>n;
        int arr[27]={0};
        for(int i=0;i<n;i++){
            char c;
            cin>>c;
            arr[(int)c-96]=1;
        }
        int mx = INT_MIN;
        for(int i=1;i<27;i++){
            if(arr[i]==1)   mx = i;
        }
        cout<<mx<<endl;
    }
}