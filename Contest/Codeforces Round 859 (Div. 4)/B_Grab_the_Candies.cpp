#include <bits/stdc++.h>
using namespace std;
  int main(){
    int t;
    cin>>t;
    while(t--){
        int n,x,m=0 ,b=0;
        cin>>n;
        for(int i=0;i<n;i++){
            cin>>x;
            if(x%2==0)  m+=x;
            else b+=x;
        }
        if(m>b) cout<<"YES"<<endl;
        else cout<<"NO"<<endl;
    }
}