#include <bits/stdc++.h>
using namespace std;
int main() {
    int t;
    cin>>t;
    while(t--){
        int n,x,cnt = 0;
        cin>>n;
        for(int i = 1;i<=n;i++){
            cin>>x;
            if(x==i) cnt++;
        }
        cout<<(cnt+1)/2<<endl;
    }
    return 0;
}