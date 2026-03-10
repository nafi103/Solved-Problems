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

const int N = 1e7, M = 2e5 + 10;
vector<int> spf(N + 10), pr;
int n;
vector<vector<pair<int,int>>> arr(M);

int expo(int a, int b){
    int res = 1;
    while(b > 0){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}

int mminvprime(int a){
    return expo(a, mod - 2);
}

void update(int &p, int &e, map<int,pair<int,int>> &power){
    pair<int,int> &value = power[p];
    if(value.first <= e){
        swap(value.first, value.second);
        value.first = e;
    }else if(value.second < e){
        value.second = e;
    }
}

vector<pair<int,int>> prime_factorization(int x){
    vector<pair<int,int>> prime_fact;
    while(x > 1){
        int p = spf[x], cnt = 0;
        while(x % p == 0){
            x /= p;
            cnt++;
        }
        prime_fact.emplace_back(p, cnt);
    }
    return prime_fact;
}

void solve()
{
    int n;
    cin >> n;
    map<int,pair<int,int>> power;
    for(int i = 0, x; i < n; i++){
        cin >> x;
        arr[i] = prime_factorization(x);
        for(auto &[p, e]: arr[i]){
            update(p, e, power);
        }
    }
    int l = 1;
    for(auto &[p, e]: power){
        l = (l * expo(p, e.first)) % mod;
    }
    for(int i = 0; i < n; i++){
        int tl = l;
        for(auto &[p, e]: arr[i]){
            if(e == power[p].first){
                tl = (tl * mminvprime(expo(p, power[p].first))) % mod;
                tl = (tl * expo(p, power[p].second)) % mod;
            }
        }
        cout << tl << (i == n - 1 ? '\n' : ' ');
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    for (int i = 2; i <= N; ++i) {
        if (spf[i] == 0) {
            spf[i] = i;
            pr.push_back(i);
        }
        for (int j = 0; i * pr[j] <= N; ++j) {
            spf[i * pr[j]] = pr[j];
            if (pr[j] == spf[i]) {
                break;
            }
        }
    }
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}