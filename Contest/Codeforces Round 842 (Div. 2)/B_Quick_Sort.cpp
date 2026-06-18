#include <bits/stdc++.h>
using namespace std;
 void solution(){
    int n, k,cnt=1;
    cin>>n>>k;
    vector<int> v(n);
    for (int i = 0; i < n; i++){
        cin>>v[i];
        if(v[i]==cnt)   cnt++;
    }
    cout<<(n-cnt+k)/k<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}