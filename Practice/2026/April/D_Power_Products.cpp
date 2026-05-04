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
int spf[N];

void solve()
{
    int n, k;
    cin >> n >> k;
    vector<int> arr(n), to_fill(n);
    for(int i = 0; i < n; i++)
        cin >> arr[i];
    map<int,int> cnt;
    for(int i = 0; i < n; i++){
        vector<pair<int,int>> pf = {{1, 0}};
        int tmp = arr[i], reduced = 1;
        while(tmp > 1){
            int p = spf[tmp], c = 0;
            while(tmp % p == 0){
                c++;
                tmp /= p;
            }
            pf.push_back({p, c % k});
            reduced *= pow(p, c % k);
        }
        cnt[reduced]++;
        arr[i] = reduced;
        double log_sum = 0;
        for(auto &[f, s]: pf){
            double need = (k - s) % k;
            log_sum += need * log2(f);
        }
        if(log_sum >= 34)
            continue;
        int complement = 1;
        for(auto &[f, s]: pf){
            int need = (k - s) % k;
            complement *= pow(f, need);
        }
        to_fill[i] = complement;
    }
    debug(arr)
    int ans = 0;
    for(int i = 0; i < n; i++){
        int &a = arr[i], &b = to_fill[i];
        if(cnt.count(b) == 0)
            continue;
        int c = cnt[b];
        if(a == b)
            c--;
        ans += c;
    }
    cout << ans / 2 << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    iota(spf, spf + N, 0);
    for(int i = 2; i * i < N; i++){
        if(spf[i] == i){
            for(int j = i + i; j < N; j += i)
                spf[j] = min(spf[j], i);
        }
    }
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}