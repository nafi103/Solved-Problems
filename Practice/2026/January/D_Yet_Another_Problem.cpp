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

const int N = 2e5 + 10;
int a[N], n, q, pref[N], pxor[N];
map<int,vector<int>> pos_even, pos_odd;

void input(){
    cin >> n >> q;
    for(int i = 1; i <= n; i++){
        cin >> a[i];
        pref[i] = pref[i - 1] + a[i];
        pxor[i] = pxor[i - 1] ^ a[i];
        if(i & 1)
            pos_odd[pxor[i]].push_back(i);
        else
            pos_even[pxor[i]].push_back(i);
    }
}

int even_query(int l, int r){
    if(a[l] == 0 or a[r] == 0)
        return 1;
    int to_find = pxor[l - 1];
    if(l & 1){
        if(pos_odd.count(to_find) == 0)
            return -1;
        auto it = lower_bound(all(pos_odd[to_find]), l);
        if(it != pos_odd[to_find].end() and *it <= r)
            return 2;
    }else{
        if(pos_even.count(to_find) == 0)
            return -1;
        auto it = lower_bound(all(pos_even[to_find]), l);
        if(it != pos_even[to_find].end() and *it <= r)
            return 2;
    }
    return -1;
}

void solve()
{
    input();
    int l, r;
    while(q--){
        cin >> l >> r;
        if(pref[r] - pref[l - 1] == 0){
            cout << 0 << endl;
        }else if(pxor[r] ^ pxor[l - 1]){
            cout << -1 << endl;
        }else{
            int len = (r - l + 1);
            if(len & 1){
                cout << 1 << endl;
            }else{
                cout << even_query(l, r) << endl;
            }
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}