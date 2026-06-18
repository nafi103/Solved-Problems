#include <bits/stdc++.h>
#define ll long long
using namespace std;
int main() {
    int t;
    cin>>t;
    while(t--){
        ll n, ans = 1;
        cin >> n;
        while(ans++){
            if(n%ans!=0) break;
        }
        cout<<--ans<<endl;
    }
    return 0;
}