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
    int n, m, l;
    cin >> n >> m >> l;
    deque<int> d(n);
    multiset<int> s;
    for(int i = 0; i < min(n + 1, m); i++){
        s.insert(0);
    }
    for(int i = 0; i < n; i++){
        cin >> d[i];
    }
    for(int i = 1; i <= l; i++){
        int target = (sz(d) ? *s.begin() : *s.rbegin());
        s.erase(s.find(target));
        s.insert(target + 1);
        if(sz(d) and d.front() == i){
            d.pop_front();
            s.erase(s.find(*s.rbegin()));
            if(sz(d) >= sz(s))
                s.insert(0);
        }
    }
    cout << *s.rbegin() << endl;
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