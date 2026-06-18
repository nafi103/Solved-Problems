#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 void solve()
{
    int n;
    cin >> n;
    vector<int> two, three, six, cp;
    for(int i = 0, x; i < n; i++){
        cin >> x;
        int g = gcd(x, 6);
        if(g == 2){
            two.push_back(x);
        }else if(g == 3){
            three.push_back(x);
        }else if(g == 6){
            six.push_back(x);
        }else{
            cp.push_back(x);
        }
    }
    for(auto &x: two)
        cout << x << " ";
    for(auto &x: cp){
        cout << x << " "; 
    }
    for(auto &x: three){
        cout << x << " ";
    }
    for(auto &x: six)
        cout << x << " ";
    cout << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}