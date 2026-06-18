#include <bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n;
        cin>>n;
        if(n==3) cout<<"NO"<<endl;
        else if(n%2==0){
            cout<<"YES"<<endl;
            for (int i = 0; i < n; i++)
            {
                if(i%2==0)  cout<<"1 ";
                else cout<<"-1 ";
            }
            cout<<endl;
        }else{
            cout<<"YES"<<endl;
            for(int i = 0; i < n; i++){
                if(i%2==0) cout<<n/2-1<<" ";
                else cout<<"-"<<n/2<<" ";
            }
            cout<<endl;
        }
    }
}