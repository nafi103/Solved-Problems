#include <bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n,k;
        cin>>n>>k;
        int p1 = n, p2 = 1;
        for(int i=0;i<n;i++){
            if(i%2==0){
                cout<<p1<<" ";
                p1--;
            } else{
                cout<<p2<<" ";
                p2++;
            }
        }
        cout<<endl;
    }
}