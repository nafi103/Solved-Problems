#include<bits/stdc++.h>
using namespace std;
void solve(){
    int n;
    cin >> n;
    cout << (1ll << (int)(log2(n))) << '\n';
}
int main(){
    int tc;
    cin >> tc;

    while(tc --){
        solve();
    }
    return 0;
}