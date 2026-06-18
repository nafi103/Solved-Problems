#include<bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n,flag = true;
        cin>>n;
        vector<int>arr1(n),arr2(n);
        for(int i=0;i<n;i++){
            cin>>arr1[i];
        }
        for(int i=0;i<n;i++){
            cin>>arr2[i];
        }
        for (int i = 0; i < n-1; i++)
        {
            if(arr1[i]>arr1[n-1]||arr2[i]>arr2[n-1])    swap(arr1[i],arr2[i]);
            if(arr1[i]>arr1[n-1]||arr2[i]>arr2[n-1]){
                flag = false;
                break;
            }
        }
        if(flag)cout<<"Yes"<<endl;
        else cout<<"No"<<endl;
    }
}