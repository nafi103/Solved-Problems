#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 int main()
{
    fastIO;
    int n, x;
    cin >> n;
    vector<int> v1, v2, v3;
    for (int i = 1; i <= n; i++)
    {
        cin >> x;
        if (x == 1)
            v1.push_back(i);
        else if (x == 2)
            v2.pb(i);
        else
            v3.pb(i);
    }
    int k = min(min(v1.size(), v2.size()), v3.size());
    if (k == 0)
        cout << 0 << endl;
    else
    {
        cout << k << endl;
        for (int i = 0; i < k; i++)
        {
            cout << v1[i] << " " << v2[i] << " " << v3[i] << endl;
        }
    }
}