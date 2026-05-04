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
    int n, k, score = 0;
    cin >> n >> k;
    string str;
    cin >> str;

    for (int i = 0; i < n; i++){
        if(str[i] == 'W'){
            score++;
            if(i and str[i - 1] == 'W')
                score++;
        }
    }

    if(n == 1){
        cout << (score or k ? 1 : 0) << endl;
        return;
    }

    int cnt = 0, cl = 0, cr = 0;
    int l = 0, r = n - 1;

    while(l < n and str[l] == 'L'){
        l++;
        cl++;
    }
    while(r >= 0 and str[r] == 'L'){
        r--;
        cr++;
    }

    if(l > r){
        cout << max(0ll, min(n * 2 - 1, k * 2 - 1)) << endl;
        return;
    }

    vector<int> pf;
    for (int i = l; i <= r; i++){
        if(str[i] == 'L')
            cnt++;
        else{
            if(cnt)
                pf.push_back(cnt);
            cnt = 0;
        }
    }
    if(cnt)
        pf.push_back(cnt);

    sort(all(pf), greater<int>());
    while(!pf.empty() and k){
        int c = pf.back();
        pf.pop_back();
        if(c <= k){
            score += 2 * c + 1;
            k -= c;
        }else{
            score += k * 2;
            k = 0;
        }
    }
    if(cl and k){
        if(cl <= k){
            score += 2 * cl;
            k -= cl;
        }else{
            score += 2 * k;
            k = 0;
        }
    }
    if(cr and k){
        if(cr <= k){
            score += 2 * cr;
            k -= cr;
        }else{
            score += 2 * k;
            k = 0;
        }
    }
    cout << max(0ll, min(n * 2 - 1, score)) << endl;
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