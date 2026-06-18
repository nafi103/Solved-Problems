#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 void solve()
{
    int a,b,c,d;
    cin >> a >> b >> c >> d;
    if(a * b == 1){
        cout << c << " " << d << endl;
        return;
    }
    vector<int> da, db;
    da.reserve(1500); db.reserve(1500);
    for(int i = 1; i * i <= a; i++){
        if(a % i == 0){
            da.push_back(i);
            if(i * i != a)
                da.push_back(a / i);
        }
    }
    for(int i = 1; i * i <= b; i++){
        if(b % i == 0){
            db.push_back(i);
            if(i * i != b)
                db.push_back(b / i);
        }
    }
    shuffle(all(da), rng);
    shuffle(all(db), rng);
    for(auto &ap: da){
        for(auto &bp: db){
            int m = ap * bp;
            int x = (c / m) * m;
            if(x > a){
                int rem = (a * b) / (ap * bp);
                int y = (d / rem) * rem;
                if(y > b){
                    cout << x << " " << y << endl;
                    return;
                }
            }
        }
    }
    cout << -1 << " " << -1 << endl;
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